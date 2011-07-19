#pragma once

#include "../tags/QF_BV.hpp"
#include "../tags/QF_UF.hpp"
#include "../tags/Array.hpp"
#include "../support/SMT_Tag_Mapping.hpp"
#include "../support/find_executable.hpp"

#include "../result_wrapper.hpp"

#include <iostream>
#include <fstream>
#include <boost/mpl/map/map40.hpp>
#include <boost/any.hpp>
#include <boost/function.hpp>
#include <boost/format.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/iostreams/device/file_descriptor.hpp>
#include <boost/iostreams/stream.hpp>
#include <boost/iostreams/tee.hpp>

#include <boost/spirit/include/qi.hpp>
#include <boost/tuple/tuple_io.hpp>
#include <boost/fusion/adapted/boost_tuple.hpp>
#include <boost/fusion/adapted/std_pair.hpp>

namespace metaSMT {

  struct set_symbol_table_cmd;

  std::string default_symbol_table(unsigned id) {
    char buf[64];
    sprintf(buf, "var_%u", id);
    return buf;
  }

  struct write_comment;
  namespace features {
    struct comment_api;
  } /* features */
  namespace solver {

    namespace predtags = ::metaSMT::logic::tag;
    namespace bvtags = ::metaSMT::logic::QF_BV::tag;
    namespace arraytags = ::metaSMT::logic::Array::tag;
    namespace uftags = ::metaSMT::logic::QF_UF::tag;
  
    struct lazy_string {
      
      lazy_string ()
        : dirty(false), _str(), _concats()
      {}

      lazy_string (std::string const & s)
        : dirty(false), _str(s), _concats()
      {}
      
      //operator std::string {
      //  _eval();
      //  return _str;
      //}

      size_t size() const {
        size_t ret = _str.size();
        BOOST_FOREACH( lazy_string const & ls, _concats ) {
          ret += ls.size();
        }
        return ret;
      }

      void _eval( std::string & str) {
        if( dirty ) {
          str.reserve(size());
          BOOST_FOREACH( lazy_string const & ls, _concats ) {
            //str += (std::string) ls;
          }
        }
        dirty = false;
      }

      bool dirty;
      std::string _str;
      std::list<lazy_string> _concats;
    };

    struct smt2_solver_pipe {
      smt2_solver_pipe(std::ofstream &os, std::ofstream &solution_os) 
        : os_(os)
        , solution_os_(solution_os)
        , _solver(NULL)
        , _result(NULL)
      {
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

        if(cpid == 0 ) {
          // solver process
          close(toSolver[1]);   // unused
          close(fromSolver[0]); // unused

          dup2(toSolver[0],0);
          dup2(fromSolver[1],1);
          //execlp("cat", "cat", NULL);
          std::string z3 = support::find_executable("z3", "Z3_EXECUTABLE");
          //std::cerr << "using Z3: " << z3 << std::endl;
          execlp(z3.c_str(), z3.c_str(), "-smt2", "-in", NULL);
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
      
      std::ostream & solver() {
        assert( _solver->is_open());
        return *_solver;
      }

      std::istream & result() {
        assert( _result->is_open());
        return *_result;
      }

      void get_response(std::string & response)
      {
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
        os_ << ";; " << response << std::endl;
        if( response != "success" ) {

          throw std::runtime_error(
              boost::str(boost::format("expected successful responsem instead got '%s'") % response).c_str());
        }
      }

      void print_response()
      {
        //std::cout << "; " << _result->rdbuf()->in_avail() << std::endl;
        std::string response;
        std::getline(*_result, response);
        os_ << ";; " << response << std::endl;
      }

      private:
        std::ofstream &os_;
        std::ofstream &solution_os_;

        typedef boost::iostreams::stream<boost::iostreams::file_descriptor_sink> solver_stream;
        solver_stream *_solver;

        typedef boost::iostreams::stream<boost::iostreams::file_descriptor_source> result_stream;
        result_stream *_result;


      template<typename Obj>
      friend
      smt2_solver_pipe & operator<< (smt2_solver_pipe & smt, Obj const & o) {
        smt.os_ << o;
        smt.solver() << o << std::flush;
        return smt;
      }
    };

    struct type_visitor : boost::static_visitor<std::string> {
      type_visitor() {}

      std::string operator() (type::BitVector const &arg) const {
        return boost::str( boost::format("(_ BitVec %u)") % arg.width );
      }

      std::string operator() (type::Boolean const &arg) const {
        return "Bool";
      }
    };

    /**
     * @ingroup Backend
     * @class SMT2 SMT2.hpp metaSMT/include/SMT2.hpp
     * @brief SMT version 2 backend
     */
    class SMT2 {

      public:
        typedef std::string result_type;

        SMT2 () 
        : _pushed(false)
        , _outfile("meta.smt2")
        , _solution_file("meta.sol")
        , out(_outfile, _solution_file)
        , table_(default_symbol_table)
        {
          //out << "(set-option interactive-mode true)\n";
          out << "(set-logic QF_ABV)\n";
          out.check_response();

          // for Z3
          out << "(set-option MODEL true)\n";
          out.check_response();

          out << ";; Generated by metaSMT\n"; 
        }

        ~SMT2() {
          out << "(exit)\n";
          out.print_response();
          _outfile.close();
        }

        void command ( write_comment const &, std::string message) {
          out << ";; " << message << '\n';
        }

        void command ( set_symbol_table_cmd const &, boost::function<std::string(unsigned)> const &table) {
          table_ = table;
        }

        void assertion( result_type e ) { 
            restore_stack();
            out << "(assert " << e << ")\n";
            out.check_response();
        }

        void assumption( result_type e ) { 
          _assumptions.push_back(e);
        }

        void restore_stack () {
          if (_pushed) {
            out << "(pop 1)\n";
            out.check_response();
            _pushed = false;
          }
        }
        
        bool solve() {
          restore_stack();
          out << "(push 1)\n";
          _pushed = true;
          out.check_response();
          BOOST_FOREACH( result_type const & r, _assumptions) {
            out << "(assert " << r << ")\n";
            out.check_response();
            
          }
          _assumptions.clear();
          out << "(check-sat)\n";
          std::string s;
          out.get_response(s);

          if ( s!= "sat" && s != "unsat" ) {
            std::string message ="unknown solver result: ";
            message += s;
            throw std::runtime_error(message);
          }

          return s== "sat";
        }

        result_wrapper read_value(result_type var)
        { 
          out << boost::format("(get-value (%s))\n") % var;
          std::string s;
          out.get_response(s);

          // predicate
          if (s == "(true)") {
            return result_wrapper(true);
          } else if (s == "(false)") {
            return result_wrapper(false);
          }

          // bitvector
          typedef std::string::const_iterator ConstIterator;
          typedef boost::tuple<unsigned, unsigned> BitvectorTuple;
          static boost::spirit::qi::rule<ConstIterator, BitvectorTuple()> bitvector_rule
            = "((_ bv" >> boost::spirit::qi::uint_ >> " " >> boost::spirit::qi::uint_ >> "))"
            ;

          BitvectorTuple bv;
          ConstIterator it = s.begin();
          ConstIterator ie = s.end();

          if (boost::spirit::qi::parse(it, ie, bitvector_rule, bv)) {
            assert( it == ie && "Expression not completely consumed" );
            return result_wrapper(bv.get<0>(), bv.get<1>());
          }

          // else
          return result_wrapper("X"); 
        }

        result_type operator() (predtags::var_tag const & var, boost::any args )
        {
          std::string buf = table_(var.id);
          restore_stack();
          out << boost::format( "(declare-fun %s () Bool)\n") % buf;
          out.check_response();
          return buf;
        }

        result_type operator() (uftags::function_var_tag const & var, boost::any args) {
          std::string buf = table_(var.id);
          restore_stack();
          out << boost::str( boost::format( "(declare-fun %s (" ) % buf );
          unsigned const num_args = var.args.size();
          for (unsigned u = 0; u < num_args; ++u) {
            out << boost::apply_visitor(type_visitor(), var.args[u]) << ' ';
          }
          out << boost::str( boost::format(") %s)\n") % boost::apply_visitor(type_visitor(), var.result_type) );
          out.check_response();
          return buf;
        }

        result_type operator() (proto::tag::function,
                                result_type func_decl) {
          return boost::str( boost::format("(%s)") );
        }

        result_type operator() (proto::tag::function,
                                result_type func_decl,
                                result_type arg) {
          return boost::str( boost::format("(%s %s)") % func_decl % arg );
        }

        result_type operator() (proto::tag::function,
                                result_type func_decl,
                                result_type arg1,
                                result_type arg2) {
          return boost::str( boost::format("(%s %s %s)") % func_decl % arg1 % arg2 );
        }

        result_type operator() (proto::tag::function,
                                result_type func_decl,
                                result_type arg1,
                                result_type arg2,
                                result_type arg3) {
          return boost::str( boost::format("(%s %s %s %s)") % func_decl % arg1 % arg2 % arg3 );
        }

        result_type operator() (predtags::false_tag , boost::any arg ) {
          return "false";
        }

        result_type operator() (predtags::true_tag , boost::any arg ) {
          return "true";
        }

        result_type operator() (bvtags::var_tag const & var, boost::any args )
        {
          assert ( var.width != 0 );
          std::string buf = table_(var.id);
          restore_stack();
          out << boost::format( "(declare-fun %s () (_ BitVec %d))\n") % buf % var.width;
          out.check_response();
          return buf;
        }

        //result_type operator() (bvtags::bit0_tag , boost::any arg ) {
        //  //return boolector_false(_btor);
        //  return "#b0";
        //}

        //result_type operator() (bvtags::bit1_tag , boost::any arg ) {
        //  //return boolector_true(_btor);
        //  return "#b1";
        //}

        result_type operator() (bvtags::bvuint_tag , boost::any arg ) {
          typedef boost::tuple<unsigned long, unsigned long> P;
          P p = boost::any_cast<P>(arg);
          unsigned value = boost::get<0>(p);
          unsigned width = boost::get<1>(p);
          return boost::str( boost::format("bv%u[%u]")%value%width);
        }

        result_type operator() (bvtags::bvsint_tag , boost::any arg ) {
          typedef boost::tuple<long, unsigned long> P;
          P p = boost::any_cast<P>(arg);
          long value = boost::get<0>(p);
          unsigned width = boost::get<1>(p);
          return boost::str( boost::format("bv%u[%u]")
            % static_cast<unsigned long>(value)
            % width
            );
        }

        result_type operator() (bvtags::bvbin_tag , boost::any arg ) {
          std::string val = boost::any_cast<std::string>(arg);
          return boost::str( boost::format("bvbin%s")%val);
          //return boost::str( boost::format("#b%s")%val);
        }

        result_type operator() (bvtags::bvhex_tag , boost::any arg ) {
          std::string hex = boost::any_cast<std::string>(arg);
          return boost::str( boost::format("bvhex%s")%hex);
          //return boost::str( boost::format("#x%s")%hex);
        }

        result_type operator() (bvtags::extract_tag const & 
            , unsigned long upper, unsigned long lower
            , result_type e)
        {
          return boost::str( boost::format( 
              "( (_ extract %u %u) %s )") %upper %lower %e );
        }

        result_type operator() (bvtags::zero_extend_tag const & 
            , unsigned long width
            , result_type e)
        {
          return boost::str( boost::format( 
              "( (_ zero_extend %u) %s )") % width% e);
        }

        result_type operator() (bvtags::sign_extend_tag const & 
            , unsigned long width
            , result_type e)
        {
          return boost::str( boost::format( 
              "( (_ sign_extend %u) %s )") % width% e);
        }

        result_type operator() (arraytags::array_var_tag const & var
                                , boost::any args )
        {
          //return boolector_array(_btor, var.elem_width, var.index_width, NULL);
          std::string buf = table_(var.id);
          restore_stack();
          out << boost::format( "(declare-fun %s () (Array (_ BitVec %d) (_ BitVec %d)))\n")
            % buf % var.index_width % var.elem_width;
          out.check_response();
          return buf;
        }
 
        result_type operator() (arraytags::select_tag const &
                                , result_type array
                                , result_type index)
        {
          //return boolector_read(_btor, array, index);
          return boost::str( boost::format(
              "(select %s %s)") % array % index);
        }

        result_type operator() (arraytags::store_tag const &
                                , result_type array
                                , result_type index
                                , result_type value)
        {
          //return boolector_write(_btor, array, index, value);
          return boost::str( boost::format(
              "(store %s %s %s)") % array % index % value);
        }

        ////////////////////////
        // Fallback operators //
        ////////////////////////

        template <typename TagT>
        result_type operator() (TagT tag, boost::any args ) {
          //return boolector_false(_btor);
          return get_tag_name(tag);
        }


        template <typename TagT>
        result_type operator() (TagT tag, result_type a ) {
          //return boolector_false(_btor);
          return std::string("(") + get_tag_name(tag) + " " + a + ")";
        }

        template <typename TagT>
        typename boost::enable_if<
          typename mpl::has_key< SMT_Negated_Map, TagT>::type
        , result_type
        >::type
        operator() (TagT tag, result_type a, result_type b) {
          typedef typename mpl::at< SMT_Negated_Map, TagT >::type p;

          return (*this)( typename p::first(), (*this)( typename p::second(), a, b)); 
        } 

        template <typename TagT>
        typename boost::disable_if<
          typename mpl::has_key< SMT_Negated_Map, TagT>::type
        , result_type
        >::type
        operator() (TagT tag, result_type a, result_type b) {
          return std::string("(") + get_tag_name(tag) + " " + a + " " + b + ")";
        }


        template <typename TagT>
        result_type operator() (TagT tag, result_type a, result_type b, result_type c) {
          return std::string("(") + get_tag_name(tag) + " " + a 
            + " " + b + " " + c + ")";
        }

      private:
        bool _pushed;
        std::ofstream _outfile;
        std::ofstream _solution_file;
        smt2_solver_pipe out;
        std::list<result_type> _assumptions;
        boost::function<std::string(unsigned)> table_;
    };
    /**@}*/
	
  } // namespace solver

  namespace features {
    template<>
    struct supports< solver::SMT2, features::comment_api>
    : boost::mpl::true_ {};

    template<>
    struct supports< solver::SMT2, set_symbol_table_cmd>
    : boost::mpl::true_ {};
  } /* features */
} // namespace metaSMT

//  vim: ft=cpp:ts=2:sw=2:expandtab
