#pragma once
#include "get_index.hpp"
#include "has_attribute.hpp"
#include "CallByIndex.hpp"
#include "UTreeToString.hpp"
#include "../SimpleSymbolTable.hpp"
#include "../../API/Assertion.hpp"
#include "../../API/Options.hpp"
#include "../../API/Stack.hpp"
#include "../../io/SMT2_ResultParser.hpp"
#include "../../types/TypedSymbol.hpp"
#include <boost/utility/enable_if.hpp>
#include <boost/type_traits/is_same.hpp>

namespace metaSMT { 
  namespace evaluator {
    namespace detail {
      template < typename ResultType >
      bool to_numeral(ResultType &result, std::string const s) {
        typedef std::string::const_iterator ConstIterator;
        static boost::spirit::qi::rule< ConstIterator, ResultType() > parser
          = boost::spirit::qi::int_
          ;

        ConstIterator it = s.begin(), ie = s.end();
        if ( boost::spirit::qi::parse(it, ie, parser, result) ) {
          assert( it == ie && "Expression not completely consumed" );
          return true;
        }

        assert( false && "Parsing failed" );
        return false;
      }
    } // detail

    namespace idx = support::idx;

    namespace cmd {
      /*
       * Note that a copy constructor is required for every command.
       * (A solver context is typically not copyable and thus passed
       * by pointer.)
       **/
      struct DefaultConstructableDummyCommand {
        typedef void result_type;

        template < typename T >
        void operator()(T const &) const {}
      }; // DefaultConstructableDummyCommand

      template < typename Context >
      class NoCommand {
      public:
        typedef void result_type;

        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

      public:
        NoCommand(Context *ctx, VarMap *var_map,
                  support::simple_symbol_table *table) {}

        result_type operator()(boost::optional<boost::spirit::utree> ut) {
          std::cerr << "ERROR: NoCommand called" << '\n';
          exit(-1);
        }
      }; // NoCommand

      template < typename Context >
      class SetLogic {
      public:
        typedef void result_type;

        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

      public:
        SetLogic(Context *ctx, VarMap *var_map,
                 support::simple_symbol_table *table)
          : ctx(ctx)
        {}

        typename boost::enable_if<
          typename features::supports<Context, set_option_cmd>::type
        , result_type
        >::type
        operator()(boost::optional<boost::spirit::utree> const &ut) {
          assert( ut );
          boost::spirit::utree::const_iterator it = ut->begin();
          it++;
          std::string const logic = utreeToString( *it );
          set_option(*ctx, "logic", logic);
        }

      protected:
        Context *ctx;
      }; // SetLogic

      template < typename Context >
      class SetInfo {
      public:
        typedef void result_type;

        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

      public:
        SetInfo(Context *ctx, VarMap *var_map,
                support::simple_symbol_table *table)
          : ctx(ctx)
        {}

        result_type operator()(boost::optional<boost::spirit::utree> const &ut) {
          std::cerr << "Warning: Ignore SMT-LIB2 set-info command" << '\n';
        }

      protected:
        Context *ctx;
      }; // SetInfo

      template < typename Context >
      class SetOption {
      public:
        typedef void result_type;

        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

      public:
        SetOption(Context *ctx, VarMap *var_map,
                  support::simple_symbol_table *table)
          : ctx(ctx)
        {}

        result_type operator()(boost::optional<boost::spirit::utree> ut) {
          std::cerr << "Warning: Ignore SMT-LIB2 set-option command" << '\n';
        }

      protected:
        Context *ctx;
      }; // SetOption

      template < typename Context >
      class GetOption {
      public:
        typedef void result_type;

        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

      public:
        GetOption(Context *ctx, VarMap *var_map,
                  support::simple_symbol_table *table)
          : ctx(ctx)
        {}

        result_type operator()(boost::optional<boost::spirit::utree> ut) {
          std::cerr << "Warning: Ignore SMT-LIB2 get-option command" << '\n';
        }

      protected:
        Context *ctx;
      }; // GetOption

      template < typename Context >
      class Assert {
      public:
        typedef void result_type;

        typedef typename Context::result_type rtype;

        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

        typedef boost::tuple< logic::index, std::vector<rtype> > command;

      public:
        Assert(Context *ctx, VarMap *var_map,
               support::simple_symbol_table *table)
          : ctx(ctx)
          , var_map(var_map)
        {}

        result_type operator()(boost::optional<boost::spirit::utree> assertion) {
          if ( assertion ) {
            boost::spirit::utree::iterator it = assertion->begin();
            assert( utreeToString(*it) == "assert" ); ++it;

            rtype r = evaluateSExpr(it, assertion->end());
            metaSMT::assertion(*ctx, r);
          }
          return result_type();
        }

        rtype SIntFromBVString(std::string const value_string, std::string const width_string) const {
          typedef std::string::const_iterator ConstIterator;
          static boost::spirit::qi::rule< ConstIterator, unsigned long() > value_parser
            = boost::spirit::qi::lit("bv") >> boost::spirit::qi::ulong_
            ;

          static boost::spirit::qi::rule< ConstIterator, unsigned() > width_parser
            = boost::spirit::qi::uint_
            ;

          ConstIterator it, ie;
          
          // parse value
          it = value_string.begin(), ie = value_string.end();
          unsigned long value;
          if ( boost::spirit::qi::parse(it, ie, value_parser, value) ) {
            assert( it == ie && "Expression not completely consumed" );
          }

          // parse width
          it = width_string.begin(), ie = width_string.end();
          unsigned width;
          if ( boost::spirit::qi::parse(it, ie, width_parser, width) ) {
            assert( it == ie && "Expression not completely consumed" );
          }

          return evaluate(*ctx, logic::QF_BV::bvsint(value, width));
        }


        rtype evaluateBooleanVarOrConstant(std::string arg) const {
          // constant true / false
          boost::optional< logic::index > idx = support::idx::get_index(arg);
          if ( idx ) {
            std::vector<rtype> rv;
            return evaluateIndex(arg,*idx,boost::make_tuple(),rv);
          }

          // variable name
          boost::optional<TypedSymbolPtr> var = getVariable(arg);
          if ( var ) {
            return (*var)->eval(*ctx);
          }

          // constant values
          typedef std::string::const_iterator ConstIterator;
          io::smt2_response_grammar<ConstIterator> parser;
          ConstIterator it = arg.begin(), ie = arg.end();
          static boost::spirit::qi::rule< ConstIterator, unsigned long() > binary_rule
            = boost::spirit::qi::lit("#b") >> boost::spirit::qi::uint_parser<unsigned long, 2, 1, 64>()
            ;
          static boost::spirit::qi::rule< ConstIterator, unsigned long() > hex_rule
            = boost::spirit::qi::lit("#x") >> boost::spirit::qi::uint_parser<unsigned long, 16, 1, 16>()
            ;

          rtype result;
          unsigned long number;
          it = arg.begin(), ie = arg.end();
          if ( boost::spirit::qi::parse(it, ie, binary_rule, number) ) {
            assert( it == ie && "Expression not completely consumed" );
            arg.erase(0, 2);
            result = evaluate(*ctx, logic::QF_BV::bvbin(arg));
          }
                
          it = arg.begin(), ie = arg.end();
          if ( boost::spirit::qi::parse(it, ie, hex_rule, number) ) {
            assert( it == ie && "Expression not completely consumed" );
            arg.erase(0, 2);
            result = evaluate(*ctx, logic::QF_BV::bvhex(arg));
          }
          return result;
        }

        rtype evaluateSExpr(boost::spirit::utree::iterator &it, boost::spirit::utree::iterator const &ie) {
          bool starts_with_bracket = false;
          if ( utreeToString(*it) == "(" ) {
            starts_with_bracket = true;
            ++it;
          }

          std::string const s = utreeToString(*it);
          assert( it != ie );
          ++it;

          // SMT-LIB2 keyword
          boost::optional<logic::index> idx = support::idx::get_index(s);
          if ( idx ) {
            std::vector<rtype> params;
            if ( support::has_attribute<attr::constant>(s) ) {
              return evaluateIndex(s,*idx,boost::make_tuple(),params);              
            }
            else if ( support::has_attribute<attr::unary>(s) ) {
              params.push_back( evaluateSExpr(it, ie) );
              ++it; // skip ')'
              return evaluateIndex(s,*idx,boost::make_tuple(),params);
            }
            else if ( support::has_attribute<attr::binary>(s) ) {
              params.push_back( evaluateSExpr(it, ie) );
              params.push_back( evaluateSExpr(it, ie) );
              ++it; // skip ')'
              return evaluateIndex(s,*idx,boost::make_tuple(),params);
            }
            else if ( support::has_attribute<attr::ternary>(s) ) {
              params.push_back( evaluateSExpr(it, ie) );
              params.push_back( evaluateSExpr(it, ie) );
              params.push_back( evaluateSExpr(it, ie) );
              ++it; // skip ')'
              return evaluateIndex(s,*idx,boost::make_tuple(),params);
            }
            else if ( support::has_attribute<attr::right_assoc>(s) ||
                      support::has_attribute<attr::left_assoc>(s) ||
                      support::has_attribute<attr::chainable>(s) ||
                      support::has_attribute<attr::pairwise>(s) ) {
              while ( it != ie && utreeToString(*it) != ")" ) {
                params.push_back( evaluateSExpr(it, ie) );
              }
              ++it; // skip ')'
              return evaluateIndex(s,*idx,boost::make_tuple(),params);
            }
          }
          else if ( s == "(" ) {
            assert( utreeToString(*it) == "_" );
            ++it;

            std::string const value = utreeToString(*it);
            ++it;

            boost::optional<logic::index> idx = support::idx::get_index(value);
            assert( idx );

            if ( *idx == logic::Index<bvtags::zero_extend_tag>::value ||
                 *idx == logic::Index<bvtags::sign_extend_tag>::value ) {
              std::vector<rtype> params;
              unsigned long op0;
              detail::to_numeral(op0, utreeToString(*it++));
              ++it; // skip ')'
              while ( it != ie && utreeToString(*it) != ")" ) {
                params.push_back( evaluateSExpr(it, ie) );
              }
              ++it; // skip ')'
              return evaluateIndex(value,*idx,boost::make_tuple(op0),params);
            }
            else if ( *idx == logic::Index<bvtags::extract_tag>::value ) {
              std::vector<rtype> params;
              unsigned long op0;
              detail::to_numeral(op0, utreeToString(*it++));
              unsigned long op1;
              detail::to_numeral(op1, utreeToString(*it++));
              ++it; // skip ')'
              while ( it != ie && utreeToString(*it) != ")" ) {
                params.push_back( evaluateSExpr(it, ie) );
              }
              ++it; // skip ')'
              return evaluateIndex(value,*idx,boost::make_tuple(op0,op1),params);
            }
            else {
              assert( false && "Yet not supported");
            }

            assert( false );
          }
          else if ( s == "_" ) {
            std::string const value = utreeToString(*it);
            ++it;
            boost::optional<logic::index> idx = support::idx::get_index(value);
            assert( !idx );
            std::string size = utreeToString(*it++);
            ++it;
            return SIntFromBVString(value,size);
          }
          return evaluateBooleanVarOrConstant(s);
        }

        template < typename Arg >
        rtype evaluateIndex(std::string const &op, logic::index const &idx,
                                  Arg arg, std::vector<rtype> params) const {
          if ( support::has_attribute<attr::constant>(op) ) {
            assert( params.size() == 0 );
            return support::idx::CallByIndex<Context>(*ctx)(idx, arg);
          }
          else if ( support::has_attribute<attr::unary>(op) ) {
            assert( params.size() == 1 );
            return support::idx::CallByIndex<Context>(*ctx)(idx, arg, params[0]);
          }
          else if ( support::has_attribute<attr::binary>(op) ) {
            assert( params.size() == 2 );
            return support::idx::CallByIndex<Context>(*ctx)(idx, arg, params[0], params[1]);
          }
          else if ( support::has_attribute<attr::ternary>(op) ) {
            assert( params.size() == 3 );
            return support::idx::CallByIndex<Context>(*ctx)(idx, arg, params[0], params[1], params[2]);
          }
          else if ( support::has_attribute<attr::right_assoc>(op) ||
                    support::has_attribute<attr::left_assoc>(op) ||
                    support::has_attribute<attr::chainable>(op) ||
                    support::has_attribute<attr::pairwise>(op) ) {
            return support::idx::CallByIndex<Context>(*ctx)(idx, arg, params);
          }
          assert( false && "Yet not implemented operator" );
          return rtype();
        }


        boost::optional<TypedSymbolPtr>
        getVariable( std::string const &name ) const {
          typename VarMap::const_iterator it = var_map->find(name);
          if (it != var_map->end()) {
            return boost::optional<TypedSymbolPtr>(it->second);
          }
          else {
            return boost::optional<TypedSymbolPtr>();
          }
        }

      protected:
        Context *ctx;
        VarMap *var_map;
      }; // Assert

      template < typename Context >
      class CheckSat {
      public:
        typedef bool result_type;

        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

      public:
        CheckSat(Context *ctx, VarMap *var_map,
                 support::simple_symbol_table *table)
          : ctx(ctx)
        {}

        result_type operator()(boost::optional<boost::spirit::utree> ut) {
          return solve(*ctx); 
        }

      protected:
        Context *ctx;
      }; // CheckSat

      template < typename Context >
      class GetValue {
      public:
        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

        typedef boost::tuple<std::string, TypedSymbolPtr> result_type;

      public:
        GetValue(Context *ctx, VarMap *var_map,
                 support::simple_symbol_table *table)
          : ctx(ctx)
          , var_map(var_map)
        {}

        result_type operator()(boost::optional<boost::spirit::utree> ast) {
          assert( ast );
          boost::spirit::utree::iterator it = ast->begin();
          assert( utreeToString(*it) == "get-value" );
          ++it;

          assert( utreeToString(*it) == "(" );
          ++it; // skip "("

          std::string const name = utreeToString(*it);
          boost::optional<TypedSymbolPtr> var = getVariable(name);
          if (!var) {
            assert( false && "Could not determine variable" );
          }
          // result_wrapper result = read_value(*ctx, (*var)->eval(*ctx));
          return boost::make_tuple(name,*var);
        }

        boost::optional<TypedSymbolPtr>
        getVariable( std::string const &name ) const {
          typename VarMap::const_iterator it = var_map->find(name);
          if (it != var_map->end()) {
            return boost::optional<TypedSymbolPtr>(it->second);
          }
          else {
            return boost::optional<TypedSymbolPtr>();
          }
        }

        Context *ctx;
        VarMap *var_map;
      }; // GetValue

      template < typename Context >
      class DeclareFun {
      public:
        typedef void result_type;

        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

      public:
        DeclareFun(Context *ctx, VarMap *var_map,
                   support::simple_symbol_table *table)
          : ctx(ctx)
          , var_map(var_map)
          , table(table)
        {}

        result_type operator()( boost::optional<boost::spirit::utree> decl ) {
          if ( !decl ) return result_type();
          unsigned const size = decl->size();
          assert( size > 0 );

          boost::spirit::utree::iterator it = decl->begin();

          // check command name
          assert( utreeToString(*it) == "declare-fun" );
          ++it;

          // get name
          std::string const name = utreeToString(*it);
          // std::cout << "name = " << name << '\n';
          ++it;
          ++it; // skip '('
          ++it; // skip ')'

          std::string const type_string = utreeToString(*it);
          if ( type_string == "Bool" ) {
            // Bool, e.g., (declare-fun var_1 () Bool)
            logic::predicate p = logic::new_variable();
            (*var_map)[name] = TypedSymbolPtr(new TypedSymbol(p));
            table->insert( p, name );
          }
          else if ( type_string == "(" ) {
            // Bit-Vec, e.g., (declare-fun var_1 () (_ BitVec 1))
            ++it;
            assert( utreeToString(*it) == "_" );

            ++it;
            std::string const type_name = utreeToString(*it);
            if ( type_name == "BitVec" ) {
              ++it;
              unsigned w;
              detail::to_numeral( w, utreeToString(*it) );
              logic::QF_BV::bitvector bv = logic::QF_BV::new_bitvector(w);
              (*var_map)[name] = TypedSymbolPtr(new TypedSymbol(bv, w));
              table->insert( bv, name );
            }
            else {
              assert( false );
              std::cerr << "ERROR: declare-fun with unsupported function type\n";
              exit(-1);
            }
          }
        }

      protected:
        Context *ctx;
        VarMap *var_map;
        support::simple_symbol_table *table;
      }; // DeclareFun

      template < typename Context >
      class Push {
      public:
        typedef void result_type;

        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

      public:
        Push(Context *ctx, VarMap *var_map,
             support::simple_symbol_table *table)
          : ctx(ctx)
        {}

        result_type operator()(boost::optional<boost::spirit::utree> tree) {
          if ( tree ) {
            boost::spirit::utree::iterator it = tree->begin();
            assert( utreeToString(*it) == "push" );
            ++it;
            unsigned how_many;
            detail::to_numeral(how_many, utreeToString(*it));
            metaSMT::push(*ctx, how_many);
          }
        }

      protected:
        Context *ctx;
      }; // Push

      template < typename Context >
      class Pop {
      public:
        typedef void result_type;

        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

      public:
        Pop(Context *ctx, VarMap *var_map,
            support::simple_symbol_table *table)
          : ctx(ctx)
        {}

        result_type operator()(boost::optional<boost::spirit::utree> tree) {
          if ( tree ) {
            boost::spirit::utree::iterator it = tree->begin();
            assert( utreeToString(*it) == "pop" );
            ++it;
            unsigned how_many;
            detail::to_numeral(how_many, utreeToString(*it));
            metaSMT::pop(*ctx, how_many);
          }
        }

      protected:
        Context *ctx;
      }; // Pop

      template < typename Context >
      class Exit {
      public:
        typedef void result_type;

        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

      public:
        Exit(Context *ctx, VarMap *var_map,
             support::simple_symbol_table *table)
          : ctx(ctx)
        {}

        result_type operator()(boost::optional<boost::spirit::utree> ut) {
          std::cerr << "Exit called" << '\n';
        }

      protected:
        Context *ctx;
      }; // Exit
    } // cmd
  } // evaluator
} // metaSMT
