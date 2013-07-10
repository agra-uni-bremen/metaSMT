#pragma once
// lazy includes
#include "get_index.hpp"
#include "has_attribute.hpp"
#include "CallByIndex.hpp"

#include "../../API/Stack.hpp"
#include "../../io/SMT2_ResultParser.hpp"
#include "../../types/TypedSymbol.hpp"

#include <boost/lexical_cast.hpp>
#include <stack>

namespace metaSMT {
  namespace evaluator {
    std::string utreeToString(boost::spirit::utree const tree) {
      std::stringstream ss;
      ss << tree;
      std::string output = ss.str();

      std::size_t found = output.find("\"");
      while (found != output.npos) {
        output.erase(found, 1);
        found = output.find("\"");
      }
      found = output.find(" ");
      while (found != output.npos) {
        output.erase(found, 1);
        found = output.find(" ");
      }

      if ( output == "(" || output == ")" ) {
        return output;
      }

      found = output.find("(");
      while (found != output.npos) {
        output.erase(found, 1);
        found = output.find("(");
      }
      found = output.find(")");
      while (found != output.npos) {
        output.erase(found, 1);
        found = output.find(")");
      }
      return output;
    }

    namespace idx = support::idx;

    namespace cmd {
      class NoCommand {
      public:
        NoCommand()
        {}

        void operator()(boost::optional<boost::spirit::utree> ut) {
          std::cerr << "ERROR: NoCommand called" << '\n';
          exit(-1);
        }
      }; // NoCommand

      template < typename Context >
      class SetLogic {
      public:
        SetLogic(Context &ctx)
          : ctx(ctx)
        {}

        void operator()(boost::optional<boost::spirit::utree> ut) {
          std::cerr << "Warning: Ignore SMT-LIB2 setlogic command" << '\n';
        }

      protected:
        Context &ctx;
      }; // SetLogic

      template < typename Context >
      class SetInfo {
      public:
        SetInfo(Context &ctx)
          : ctx(ctx)
        {}

        void operator()(boost::optional<boost::spirit::utree> ut) {
          std::cerr << "Warning: Ignore SMT-LIB2 set-info command" << '\n';
        }

      protected:
        Context &ctx;
      }; // SetInfo

      template < typename Context >
      class SetOption {
      public:
        SetOption(Context &ctx)
          : ctx(ctx)
        {}

        void operator()(boost::optional<boost::spirit::utree> ut) {
          std::cerr << "Warning: Ignore SMT-LIB2 setoption command" << '\n';
        }

      protected:
        Context &ctx;
      }; // SetOption

      template < typename Context >
      class GetOption {
      public:
        GetOption(Context &ctx)
          : ctx(ctx)
        {}

        void operator()(boost::optional<boost::spirit::utree> ut) {
          std::cerr << "Warning: Ignore SMT-LIB2 getoption command" << '\n';
        }

      protected:
        Context &ctx;
      }; // GetOption

      template < typename Context >
      class Assert {
      public:
        typedef typename Context::result_type result_type;

        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

        typedef boost::tuple< logic::index, std::vector<result_type> > command;

      public:
        Assert(Context &ctx, VarMap &var_map)
          : ctx(ctx)
          , var_map(var_map)
        {}

        void operator()(boost::optional<boost::spirit::utree> assertion) {
          if ( assertion ) {
            boost::spirit::utree::iterator it = assertion->begin();
            assert( utreeToString(*it) == "assert" ); ++it;

            result_type r = evaluateSExpr(it, assertion->end());
            metaSMT::assertion(ctx, r);
          }
        }

        result_type SIntFromBVString(std::string value, std::string bitSize) const {
          unsigned long number = 0;
          if (value.size() > 2) {
            if (value.find("bv", 0, 2) != value.npos) {
              value.erase(0, 2);
              number = boost::lexical_cast<unsigned long>(value);
            }
          }

          unsigned const width = boost::lexical_cast<unsigned>(bitSize);
          if (width == 1) {
            if (number == 1) {
              return evaluate(ctx, logic::QF_BV::bit1);
            } else if (number == 0) {
              return evaluate(ctx, logic::QF_BV::bit0);
            }
          }
          return evaluate(ctx, logic::QF_BV::bvsint(number, width));
        }

        result_type evaluateBooleanVarOrConstant(std::string arg) const {
          // constant true / false
          boost::optional< logic::index > idx = support::idx::get_index(arg);
          if ( idx ) {
            std::vector<result_type> rv;
            return evaluateIndex(arg,*idx,boost::make_tuple(),rv);
          }

          // variable name
          boost::optional<TypedSymbolPtr> var = getVariable(arg);
          if ( var ) {
            return (*var)->eval(ctx);
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

          result_type result;
          unsigned long number;
          it = arg.begin(), ie = arg.end();
          if ( boost::spirit::qi::parse(it, ie, binary_rule, number) ) {
            assert( it == ie && "Expression not completely consumed" );
            arg.erase(0, 2);
            result = evaluate(ctx, logic::QF_BV::bvbin(arg));
          }
                
          it = arg.begin(), ie = arg.end();
          if ( boost::spirit::qi::parse(it, ie, hex_rule, number) ) {
            assert( it == ie && "Expression not completely consumed" );
            arg.erase(0, 2);
            result = evaluate(ctx, logic::QF_BV::bvhex(arg));
          }
          return result;
        }

        result_type evaluateSExpr(boost::spirit::utree::iterator &it, boost::spirit::utree::iterator const &ie) {
          // while ( utreeToString(*it) == "(" || utreeToString(*it) == ")" ) ++it; // skip '(' and ')'
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
            std::vector<result_type> params;
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
              std::vector<result_type> params;
              unsigned long op0 = boost::lexical_cast<int>(utreeToString(*it++));
              ++it; // skip ')'
              while ( it != ie && utreeToString(*it) != ")" ) {
                params.push_back( evaluateSExpr(it, ie) );
              }
              ++it; // skip ')'
              return evaluateIndex(value,*idx,boost::make_tuple(op0),params);
            }
            else if ( *idx == logic::Index<bvtags::extract_tag>::value ) {
              std::vector<result_type> params;
              unsigned long op0 = boost::lexical_cast<int>(utreeToString(*it++));
              unsigned long op1 = boost::lexical_cast<int>(utreeToString(*it++));
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
        result_type evaluateIndex(std::string const &op, logic::index const &idx, Arg arg, std::vector<result_type> params) const {
          if ( support::has_attribute<attr::constant>(op) ) {
            assert( params.size() == 0 );
            return support::idx::CallByIndex<Context>(ctx)(idx, arg);
          }
          else if ( support::has_attribute<attr::unary>(op) ) {
            assert( params.size() == 1 );
            return support::idx::CallByIndex<Context>(ctx)(idx, arg, params[0]);
          }
          else if ( support::has_attribute<attr::binary>(op) ) {
            assert( params.size() == 2 );
            return support::idx::CallByIndex<Context>(ctx)(idx, arg, params[0], params[1]);
          }
          else if ( support::has_attribute<attr::ternary>(op) ) {
            assert( params.size() == 3 );
            return support::idx::CallByIndex<Context>(ctx)(idx, arg, params[0], params[1], params[2]);
          }
          else if ( support::has_attribute<attr::right_assoc>(op) ||
                    support::has_attribute<attr::left_assoc>(op) ||
                    support::has_attribute<attr::chainable>(op) ||
                    support::has_attribute<attr::pairwise>(op) ) {
            return support::idx::CallByIndex<Context>(ctx)(idx, arg, params);
          }
          assert( false && "Yet not implemented operator" );
          return result_type();
        }


        boost::optional<TypedSymbolPtr>
        getVariable( std::string const &name ) const {
          typename VarMap::const_iterator it = var_map.find(name);
          if (it != var_map.end()) {
            return boost::optional<TypedSymbolPtr>(it->second);
          }
          else {
            return boost::optional<TypedSymbolPtr>();
          }
        }

      protected:
        Context &ctx;
        VarMap &var_map;
        std::stack<command> the_stack;
      }; // Assert

      template < typename Context >
      class CheckSat {
      public:
        CheckSat(Context &ctx)
          : ctx(ctx)
        {}

        bool operator()(boost::optional<boost::spirit::utree> ut) {
          bool const sat = solve(ctx); 
          if ( sat ) {
            std::cout << "sat" << std::endl;
          } else {
            std::cout << "unsat" << std::endl;
          }
          return sat;
        }

      protected:
        Context &ctx;
      }; // CheckSat

      template < typename Context >
      class GetValue {
      public:
        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

        GetValue(Context &ctx, VarMap &var_map)
          : ctx(ctx)
          , var_map(var_map)
        {}

        boost::optional<TypedSymbolPtr>
        getVariable( std::string const &name ) const {
          typename VarMap::const_iterator it = var_map.find(name);
          if (it != var_map.end()) {
            return boost::optional<TypedSymbolPtr>(it->second);
          }
          else {
            return boost::optional<TypedSymbolPtr>();
          }
        }

        void operator()(boost::optional<boost::spirit::utree> ast) {
          if ( ast ) {
            boost::spirit::utree::iterator it = ast->begin();
            assert( utreeToString(*it) == "get-value" );
            ++it;

            assert( utreeToString(*it) == "(" );
            ++it; // skip "("

            std::string const s = utreeToString(*it);
            boost::optional<TypedSymbolPtr> var = getVariable(s);
            if (!var) {
              assert( false && "Could not determine variable" );
            }

            if ( (*var)->isBool() ) {
              bool b = read_value(ctx, (*var)->eval(ctx));
              std::cout << "((" << s << " " << (b ? "true" : "false") << "))" << '\n';
            }
            else if ( (*var)->isBitVector() ) {
              std::cout << "((" << s << " #b" << read_value(ctx, (*var)->eval(ctx)) << "))" << '\n';
            }
            else {
              assert( false && "Variable type is not supported" );
            }            
          }
        }

      protected:
        Context &ctx;
        VarMap &var_map;
      }; // GetValue

      template < typename Context >
      class DeclareFun {
      public:
        typedef type::TypedSymbol<Context> TypedSymbol;
        typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
        typedef std::map<std::string, TypedSymbolPtr > VarMap;

        DeclareFun(Context &ctx, VarMap &var_map)
          : ctx(ctx)
          , var_map(var_map)
        {}

        void operator()( boost::optional<boost::spirit::utree> decl ) {
          if ( !decl ) return;
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
            var_map[name] = TypedSymbolPtr(new TypedSymbol(logic::new_variable()));            
          }
          else if ( type_string == "(" ) {
            // Bit-Vec, e.g., (declare-fun var_1 () (_ BitVec 1))
            ++it;
            assert( utreeToString(*it) == "_" );

            ++it;
            std::string const type_name = utreeToString(*it);
            if ( type_name == "BitVec" ) {
              ++it;
              unsigned const w = boost::lexical_cast<unsigned>(utreeToString(*it));
              var_map[name] = TypedSymbolPtr(new TypedSymbol(logic::QF_BV::new_bitvector(w), w));              
            }
            else {
              assert( false );
              std::cerr << "ERROR: declare-fun with unsupported function type\n";
              exit(-1);
            }
          }
        }

      protected:
        Context &ctx;
        VarMap &var_map;
      }; // DeclareFun

      template < typename Context >
      class Push {
      public:
        Push(Context &ctx)
          : ctx(ctx)
        {}

        void operator()(boost::optional<boost::spirit::utree> tree) {
          if ( tree ) {
            boost::spirit::utree::iterator it = tree->begin();
            assert( utreeToString(*it) == "push" );
            ++it;
            unsigned how_many = boost::lexical_cast<unsigned>( utreeToString(*it) );
            metaSMT::push(ctx, how_many);
          }
        }

      protected:
        Context &ctx;
      }; // Push

      template < typename Context >
      class Pop {
      public:
        Pop(Context &ctx)
          : ctx(ctx)
        {}

        void operator()(boost::optional<boost::spirit::utree> tree) {
          if ( tree ) {
            boost::spirit::utree::iterator it = tree->begin();
            assert( utreeToString(*it) == "pop" );
            ++it;
            unsigned how_many = boost::lexical_cast<unsigned>( utreeToString(*it) );
            metaSMT::pop(ctx, how_many);
          }
        }

      protected:
        Context &ctx;
      }; // Pop

      template < typename Context >
      class Exit {
      public:
        Exit(Context &ctx)
          : ctx(ctx)
        {}

        void operator()(boost::optional<boost::spirit::utree> ut) {
          std::cerr << "Exit called" << '\n';
        }

      protected:
        Context &ctx;
      }; // Exit
    } // cmd
  } // evaluator
} // metaSMT
