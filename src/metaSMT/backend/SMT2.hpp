#pragma once

#include "../tags/QF_BV.hpp"
#include "../tags/QF_UF.hpp"
#include "../tags/Array.hpp"
#include "../support/SMT_Tag_Mapping.hpp"
#include "../support/find_executable.hpp"
#include "../io/SMT2_ResultParser.hpp"
#include "../API/SymbolTable.hpp"
#include "../support/Options.hpp"

#include "../result_wrapper.hpp"

#include "../expression/expression.hpp"
#include "../expression/pretty_printing.hpp"
#include "../expression/print_expression.hpp"
#include "../expression/simplify.hpp"

#include <iostream>
#include <fstream>
#include <boost/mpl/map/map40.hpp>
#include <boost/any.hpp>
#include <boost/function.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/iostreams/device/file_descriptor.hpp>
#include <boost/iostreams/stream.hpp>
#include <boost/iostreams/tee.hpp>

#include <boost/spirit/include/qi.hpp>
#include <boost/tuple/tuple_io.hpp>
#include <boost/fusion/adapted/boost_tuple.hpp>
#include <boost/fusion/adapted/std_pair.hpp>
#include <boost/assign.hpp>
#include <boost/algorithm/string/replace.hpp>

namespace metaSMT {
  struct stack_pop;
  struct stack_push;
  struct set_symbol_table_cmd;
  struct simplify_cmd;
  struct write_comment;
  struct setup_option_map_cmd;
  struct get_option_cmd;
  struct set_option_cmd;

  namespace features {
    struct stack_api;
    struct comment_api;
  } // features

  namespace solver {
    namespace predtags = ::metaSMT::logic::tag;
    namespace bvtags = ::metaSMT::logic::QF_BV::tag;
    namespace arraytags = ::metaSMT::logic::Array::tag;
    namespace uftags = ::metaSMT::logic::QF_UF::tag;
    namespace expr = ::metaSMT::expression;

    struct smt2_solver_pipe {
      typedef boost::iostreams::stream<boost::iostreams::file_descriptor_sink> solver_stream;
      typedef boost::iostreams::stream<boost::iostreams::file_descriptor_source> result_stream;

      smt2_solver_pipe(std::string const &executable,
                       std::vector< std::string > args,
                       std::ofstream &os,
                       std::ofstream &solution_os,
                       boost::function<std::string(unsigned)> &table)
        : os_(os)
        , solution_os_(solution_os)
        , table_(table)
        , _solver(NULL)
        , _result(NULL) {
        int toSolver[2];
        int fromSolver[2];
        if ( pipe(toSolver) == -1 || pipe(fromSolver) == -1 ) {
          throw std::runtime_error("opening pipe failed");
        }
        int cpid = fork();
        if( cpid == -1) {
          close(toSolver[0]);
          close(toSolver[1]);
          close(fromSolver[0]);
          close(fromSolver[1]);
          throw std::runtime_error("fork failed");
        }

        if ( cpid == 0 ) {
          // solver process
          close(toSolver[1]);   // unused
          close(fromSolver[0]); // unused
          dup2(toSolver[0],0);
          dup2(fromSolver[1],1);
          // std::cerr << "[DBG] Solver: " << executable << std::endl;
          support::execvp(executable.c_str(), args);
          perror("exec");
          exit(1);
        } else {
          // parent writes solution
          close(toSolver[0]);   // unused
          close(fromSolver[1]); // unused

          _solver = new solver_stream(toSolver[1], boost::iostreams::close_handle);
          _result = new result_stream(fromSolver[0], boost::iostreams::close_handle);
        }
      }

      ~smt2_solver_pipe() {
        delete _solver;
        delete _result;
      }

      std::ostream &solver() {
        assert( _solver->is_open());
        return *_solver;
      }

      std::istream &result() {
        assert( _result->is_open());
        return *_result;
       }

      void get_response( std::string  &response ) {
        //std::cout << "; " << _result->rdbuf()->in_avail() << std::endl;
        std::getline(*_result, response);
        os_ << ";; " << response << std::endl;
        if (response == "sat" || response == "unsat") {
          solution_os_ << response << std::endl;
        }
      }

      void check_response() {
        std::string response;
        std::getline(*_result, response);
      }

      void print_response() {
        //std::cout << "; " << _result->rdbuf()->in_avail() << std::endl;
        std::string response;
        std::getline(*_result, response);
        os_ << ";; " << response << std::endl;
      }

    private:
      std::ofstream &os_;
      std::ofstream &solution_os_;

      boost::function<std::string(unsigned)> &table_;

      solver_stream *_solver;
      result_stream *_result;

      template<typename Obj>
      friend
      smt2_solver_pipe & operator<< (smt2_solver_pipe & smt, Obj const & o) {
        smt.os_ << o;
        smt.solver() << o << std::flush;
        return smt;
      }

      friend
      smt2_solver_pipe &operator<< (smt2_solver_pipe &smt, expression::logic_expression const &e) {
        std::ostream_iterator<char> it(std::ostream_iterator<char>(smt.os_));
        expression::print_expression_static(it, e, smt.table_);
        std::ostream_iterator<char> solver_it(std::ostream_iterator<char>(smt.solver()));
        expression::print_expression_static(solver_it, e, smt.table_);
        smt.solver() << std::flush;
        return smt;
      }
    }; // smt2_solver_pipe

    /**
     * @ingroup Backend
     * @class SMT2 SMT2.hpp metaSMT/backend/SMT2.hpp
     * @brief SMT2 backend
     */
    class SMT2 {
    public:
      typedef expression::logic_expression result_type;

      SMT2()
        : init_(false)
        , pushed_(false)
        , table_( support::default_symbol_table )
      {}

      ~SMT2() {
        out() << "(exit)\n";
        out().check_response();
        out_file_->close();
        sol_file_->close();
      }

      void split(std::vector<std::string> &args, std::string const &s) {
        std::istringstream iss(s);
        do {
          std::string arg;
          iss >> arg;
          if ( arg != "" ) {
            args.push_back(arg);
          }
        } while (iss);
      }

      void initialize() {
        init_ = true;
        std::string smt_filename = opt_.get("smt_filename", "meta.smt2");
        out_file_.reset( new std::ofstream(smt_filename.c_str()) );
        std::string sol_filename = opt_.get("sol_filename", "meta.sol");
        sol_file_.reset( new std::ofstream(sol_filename.c_str()) );
        std::string executable = support::find_executable(opt_.get("solver_executable", "z3"), "Z3_EXECUTABLE");
        std::vector< std::string > args;
        args.push_back( executable.c_str() );
        split(args, opt_.get("solver_arguments", "-smt2 -in"));
        out_.reset( new smt2_solver_pipe(executable, args, *out_file_, *sol_file_, table_) );
        *out_ << ";; Generated by metaSMT\n";
        *out_ << "(set-logic " << opt_.get("logic", "QF_AUFBV") << ")\n";
      }

      smt2_solver_pipe &out() {
        if ( init_ ) {
          return *out_;
        }
        else {
          initialize();
          return *out_;
        }
      }

      void command( write_comment const &, std::string const &message) {
        out() << ";; " << boost::algorithm::replace_all_copy(message, "\n", "\n;; ") << '\n';
      }

      void command( set_symbol_table_cmd const &,
                    boost::function<std::string(unsigned)> const &table ) {
        table_ = table;
      }

      result_type command( simplify_cmd const &, result_type e ) {
	return expr::simplify( e );
      }

      void command( setup_option_map_cmd const &, Options const &opt ) {
        opt_ = opt;
      }

      void command( set_option_cmd const &, std::string const &key, std::string const &value, Options const &opt ) {
        if ( init_ && key == "smt_filename" && (opt_.get(key) != value) ) {
          assert( false && "Changing the filename on-the-fly is yet not allowed" );
        }
        else if ( init_ && key == "sol_filename" && (opt_.get(key) != value) ) {
          assert( false && "Changing the filename on-the-fly is yet not allowed" );
        }
        opt_ = opt;
      }

      void dump_decls( result_type e ) {
        typedef std::set< std::string > Declarations;
        Declarations decls;
        collect_decls(decls, e, table_);
        for (Declarations::const_iterator it = decls.begin(), ie = decls.end();
             it != ie; ++it) {
          // write decls only the first time
          if ( global_decls_.find(*it) == global_decls_.end() ) {
            if ( local_decls_.find(*it) == local_decls_.end() ) {
              out() << *it;
              if (pushed_) {
                local_decls_.insert(*it);
              }
              else {
                global_decls_.insert(*it);
              }
            }
          }
        }
      }

      void push() {
        out() << "(push 1)\n";
        pushed_ = true;
      }

      void pop() {
        if (pushed_) {
          out() << "(pop 1)\n";
          pushed_ = false;
          local_decls_.clear();
        }
      }

      void assertion( result_type e ) {
        assertions_.push_back( e );
      }

      void assumption( result_type e ) {
        assumptions_.push_back( e );
      }

      void command( stack_push const &, unsigned howmany ) {
        out() << "(push " << howmany << ")\n";
      }

      void command( stack_pop const &, unsigned howmany ) {
        out() << "(pop " << howmany << ")\n";
      }

      bool solve() {
        pop();
        BOOST_FOREACH( result_type const &e, assertions_ ) {
          dump_decls( e );
          out() << "(assert " << e << ")\n";
        }
        assertions_.clear();

        push();

        BOOST_FOREACH( result_type const &e, assumptions_ ) {
          dump_decls( e );
          out() << "(assert " << e << ")\n";
        }
        assumptions_.clear();

        std::string response;
        out() << "(check-sat)\n";
        out().get_response(response);
        if ( response != "sat" && response != "unsat" ) {
          std::string message = "unknown solver result: ";
          message += response;
          throw std::runtime_error(message);
        }

        return ( response == "sat" );
      }

      result_wrapper read_value( result_type const var ) {
        out() << "(get-value (" << var << "))\n";

        std::string response;
        out().get_response(response);

        // parse smt2 response
        typedef std::string::const_iterator ConstIterator;
        io::smt2_response_grammar<ConstIterator> parser;
        ConstIterator it = response.begin(), ie = response.end();

        std::string result;
        if (boost::spirit::qi::parse(it, ie, parser, result)) {
          assert( it == ie && "Expression not completely consumed" );
          if ( result == "true" ) {
            return result_wrapper( true );
          }
          else if ( result == "false" ) {
            return result_wrapper( false );
          }
        }

        // bit-vector
        static boost::spirit::qi::rule< ConstIterator, unsigned long() > binary_rule
          = boost::spirit::qi::lit("#b") >> boost::spirit::qi::uint_parser<unsigned long, 2, 1, 64>()
          ;

        static boost::spirit::qi::rule< ConstIterator, unsigned long() > hex_rule
          = boost::spirit::qi::lit("#x") >> boost::spirit::qi::uint_parser<unsigned long, 16, 1, 16>()
          ;

        unsigned long value;
        it = result.begin(), ie = result.end();
        if ( boost::spirit::qi::parse(it, ie, binary_rule, value) ) {
          assert( it == ie && "Expression not completely consumed" );
          unsigned const width = result.size() - 2;
          return result_wrapper( value, width );
        }

        it = result.begin(), ie = result.end();
        if ( boost::spirit::qi::parse(it, ie, hex_rule, value) ) {
          assert( it == ie && "Expression not completely consumed" );
          unsigned const width = (result.size() - 2)*4;
          return result_wrapper( value, width );
        }

        return result_wrapper("X");
      }

      // logic::tag
      result_type operator() ( predtags::false_tag, boost::any arg ) {
        return expr::logic_expression(false);
      }

      result_type operator() ( predtags::true_tag, boost::any arg ) {
        return expr::logic_expression(true);
      }

      result_type operator() ( predtags::not_tag, result_type arg ) {
        return expr::unary_expression<expr::logic_tag, predtags::not_tag>(arg);
      }

      result_type operator() ( predtags::equal_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::equal_tag>(a, b);
      }

      result_type operator() ( predtags::nequal_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::nequal_tag>(a, b);
      }

      result_type operator() ( predtags::and_tag, result_type a, result_type b ) {
	using namespace boost::assign;
	typedef expr::nary_expression<expr::logic_tag, predtags::and_tag> Expr;
	Expr::ContainerType v;
	v.push_back(a);
  v.push_back(b);
	return Expr(v);

      }

      result_type operator() ( predtags::nand_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::nand_tag>(a, b);
      }

      result_type operator() ( predtags::or_tag, result_type a, result_type b ) {
	using namespace boost::assign;
	typedef expr::nary_expression<expr::logic_tag, predtags::or_tag> Expr;
	Expr::ContainerType v;
	v.push_back(a);
  v.push_back(b);
	return Expr(v);
      }

      result_type operator() ( predtags::nor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::nor_tag>(a, b);
      }

      result_type operator() ( predtags::xor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::xor_tag>(a, b);
      }

      result_type operator() ( predtags::xnor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::xnor_tag>(a, b);
      }

      result_type operator() ( predtags::implies_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::implies_tag>(a, b);
      }

      result_type operator() ( predtags::ite_tag, result_type a, result_type b, result_type c ) {
        return expr::ternary_expression<expr::logic_tag, predtags::ite_tag>(a, b, c);
      }

      result_type operator() ( predtags::var_tag const &tag, boost::any a ) {
	if ( tag.id == 0 ) {
	  throw std::exception();
	}
        return proto::make_expr< proto::tag::terminal, logic::Predicate_Domain >( tag );
      }

      // logic::QF_BV::tag
      result_type operator() ( bvtags::bit0_tag , boost::any arg ) {
        return logic::QF_BV::bit0;
      }

      result_type operator() ( bvtags::bit1_tag , boost::any arg ) {
        return logic::QF_BV::bit1;
      }

      result_type operator() ( bvtags::var_tag const &tag, boost::any a ) {
	if ( tag.id == 0 ) {
	  throw std::exception();
	}
        return proto::make_expr< proto::tag::terminal, logic::QF_BV::QF_BV_Domain >( tag );
      }

      result_type operator() ( bvtags::bvnot_tag, result_type a ) {
        return expr::unary_expression<expr::bv_tag, bvtags::bvnot_tag>(a);
      }

      result_type operator() ( bvtags::bvneg_tag, result_type a ) {
        return expr::unary_expression<expr::bv_tag, bvtags::bvneg_tag>(a);
      }

      result_type operator() ( bvtags::bvand_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvand_tag>(a, b);
      }

      result_type operator() ( bvtags::bvnand_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvnand_tag>(a, b);
      }

      result_type operator() ( bvtags::bvor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvor_tag>(a, b);
      }

      result_type operator() ( bvtags::bvnor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvnor_tag>(a, b);
      }

      result_type operator() ( bvtags::bvxor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvxor_tag>(a, b);
      }

      result_type operator() ( bvtags::bvxnor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvxnor_tag>(a, b);
      }

      result_type operator() ( bvtags::bvshl_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvshl_tag>(a, b);
      }

      result_type operator() ( bvtags::bvshr_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvshr_tag>(a, b);
      }

      result_type operator() ( bvtags::bvashr_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvashr_tag>(a, b);
      }

      result_type operator() ( bvtags::bvcomp_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvcomp_tag>(a, b);
      }

      result_type operator() ( bvtags::bvadd_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvadd_tag>(a, b);
      }

      result_type operator() ( bvtags::bvmul_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvmul_tag>(a, b);
      }

      result_type operator() ( bvtags::bvsub_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvsub_tag>(a, b);
      }

      result_type operator() ( bvtags::bvsrem_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvsrem_tag>(a, b);
      }

      result_type operator() ( bvtags::bvsdiv_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvsdiv_tag>(a, b);
      }

      result_type operator() ( bvtags::bvurem_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvurem_tag>(a, b);
      }

      result_type operator() ( bvtags::bvudiv_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvudiv_tag>(a, b);
      }

      result_type operator() ( bvtags::bvuint_tag , boost::any arg ) {
        typedef boost::tuple<unsigned long, unsigned long> Tuple;
        Tuple tuple = boost::any_cast<Tuple>(arg);
        unsigned long value = boost::get<0>(tuple);
        unsigned long width = boost::get<1>(tuple);
	return expr::bv_const<bvtags::bvuint_tag>(value, width);
      }

      result_type operator() ( bvtags::bvsint_tag , boost::any arg ) {
        typedef boost::tuple<long, unsigned long> Tuple;
        Tuple const tuple = boost::any_cast<Tuple>(arg);
        long value = boost::get<0>(tuple);
        unsigned long const width = boost::get<1>(tuple);
        if (    value > std::numeric_limits<int>::max()
             || value < std::numeric_limits<int>::min()
             || (width > 8*sizeof(int) && value < 0)
          ) {
          std::string val(width, '0');
          std::string::reverse_iterator it = val.rbegin();
          for ( unsigned long u = 0; u < width; ++u, ++it ) {
            *it = (value & 1l) ? '1' : '0';
            value >>= 1;
          }
          return expr::bv_const<bvtags::bvbin_tag>::bin(val);
        }
        else {
          return expr::bv_const<bvtags::bvsint_tag>(static_cast<unsigned long>(value), width);
        }
      }

      result_type operator() ( bvtags::bvbin_tag , boost::any arg ) {
        std::string val = boost::any_cast<std::string>(arg);
	return expr::bv_const<bvtags::bvbin_tag>::bin(val);
      }

      result_type operator() ( bvtags::bvhex_tag , boost::any arg ) {
        std::string val = boost::any_cast<std::string>(arg);
	return expr::bv_const<bvtags::bvhex_tag>::hex(val);
      }

      result_type operator() ( bvtags::bvslt_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvslt_tag>(a, b);
      }

      result_type operator() ( bvtags::bvsgt_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvsgt_tag>(a, b);
      }

      result_type operator() ( bvtags::bvsle_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvsle_tag>(a, b);
      }

      result_type operator() ( bvtags::bvsge_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvsge_tag>(a, b);
      }

      result_type operator() ( bvtags::bvult_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvult_tag>(a, b);
      }

      result_type operator() ( bvtags::bvugt_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvugt_tag>(a, b);
      }

      result_type operator() ( bvtags::bvule_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvule_tag>(a, b);
      }

      result_type operator() ( bvtags::bvuge_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvuge_tag>(a, b);
      }

      result_type operator() ( bvtags::concat_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::concat_tag>(a, b);
      }

      result_type operator() ( bvtags::extract_tag const &,
                               unsigned long upper,
                               unsigned long lower,
                               result_type e ) {
        unsigned long const width = upper - lower;
        return expr::extract_expression<bvtags::extract_tag>(upper, width, e);
      }
      result_type operator() ( bvtags::zero_extend_tag const &,
                               unsigned long width,
                               result_type e ) {
        return expr::extend_expression<bvtags::zero_extend_tag>(width, e);
      }

      result_type operator() ( bvtags::sign_extend_tag const &,
                               unsigned long width,
                               result_type e ) {
        return expr::extend_expression<bvtags::sign_extend_tag>(width, e);
      }

      // logic::Array::tag
      result_type operator() ( arraytags::array_var_tag const &tag,
                               boost::any args ) {
	if ( tag.id == 0 ) {
	  throw std::exception();
	}
        return proto::make_expr< proto::tag::terminal, logic::Array::Array_Domain >( tag );
      }

      result_type operator() ( arraytags::select_tag const &,
                               result_type array,
                               result_type index ) {
        return expr::select_expression( array, index );
      }

      result_type operator() ( arraytags::store_tag const &,
                               result_type array,
                               result_type index,
                               result_type value ) {
        return expr::store_expression( array, index, value );
      }

      // logic::QF_UF::tag
      result_type operator() ( uftags::function_var_tag const &tag,
                               boost::any args ) {
	if ( tag.id == 0 ) {
	  throw std::exception();
	}
	return proto::make_expr< proto::tag::terminal, logic::QF_UF::UninterpretedFunction_Domain >( tag );
      }

      result_type operator() ( proto::tag::function const &,
                               result_type func_decl ) {
        using namespace boost::assign;
        typedef expr::nary_expression<expr::uf_tag, proto::tag::function> Func;
        Func::ContainerType v;
        v.push_back( func_decl );
        return Func(v);
      }

      result_type operator() ( proto::tag::function const &,
                               result_type func_decl,
                               result_type arg) {
        using namespace boost::assign;
        typedef expr::nary_expression<expr::uf_tag, proto::tag::function> Func;
        Func::ContainerType v;
        v.push_back(func_decl);
        v.push_back( arg );
        return Func(v);
      }

      result_type operator() ( proto::tag::function const &,
                               result_type func_decl,
                               result_type arg1,
                               result_type arg2) {
        using namespace boost::assign;
        typedef expr::nary_expression<expr::uf_tag, proto::tag::function> Func;
        Func::ContainerType v;
        v.push_back( func_decl );
        v.push_back( arg1 );
        v.push_back( arg2 );
        return Func(v);
      }

      result_type operator() ( proto::tag::function const &,
                               result_type func_decl,
                               result_type arg1,
                               result_type arg2,
                               result_type arg3) {
        using namespace boost::assign;
        typedef expr::nary_expression<expr::uf_tag, proto::tag::function> Func;
        Func::ContainerType v;
        v.push_back( func_decl );
        v.push_back( arg1 );
        v.push_back( arg2 );
        v.push_back( arg3 );
        return Func(v);
      }

      // Fallback operators
      template <typename TagT>
      result_type operator() (TagT tag, boost::any args ) {
        assert( false );
        return false;
      }

      template <typename TagT>
      result_type operator() (TagT tag, result_type a ) {
        assert( false );
        return false;
      }

      template <typename TagT>
      result_type operator() (TagT tag, result_type a, result_type b) {
        assert( false );
        return false;
      }

      template <typename TagT>
      result_type operator() (TagT tag, result_type a, result_type b, result_type c) {
        assert( false );
        return false;
      }

      bool init_;
      bool pushed_;
      Options opt_;
      boost::function<std::string(unsigned)> table_;
      boost::shared_ptr< std::ofstream > out_file_;
      boost::shared_ptr< std::ofstream > sol_file_;
      boost::shared_ptr< smt2_solver_pipe > out_;
      std::list< result_type > assumptions_;
      std::list< result_type > assertions_;
      std::set< std::string > global_decls_;
      std::set< std::string > local_decls_;
    }; // SMT2
    /**@}*/

  } // solver

  namespace features {
    template<>
    struct supports< solver::SMT2, features::stack_api >
    : boost::mpl::true_ {};

    template<>
    struct supports< solver::SMT2, features::comment_api >
    : boost::mpl::true_ {};

    template<>
    struct supports< solver::SMT2, simplify_cmd>
    : boost::mpl::true_ {};

    template<>
    struct supports< solver::SMT2, set_symbol_table_cmd >
    : boost::mpl::true_ {};

    template<>
    struct supports< solver::SMT2, setup_option_map_cmd >
    : boost::mpl::true_ {};
  } // features

} // metaSMT

//  vim: ft=cpp:ts=2:sw=2:expandtab
