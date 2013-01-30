#pragma once
#include "../tags/QF_BV.hpp"
#include "../tags/QF_UF.hpp"
#include "../tags/Array.hpp"
#include "../result_wrapper.hpp"
#include "../Features.hpp"

#include <z3++.h>

#include <boost/any.hpp>
#include <boost/mpl/map/map40.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_io.hpp>
#include <boost/fusion/adapted/boost_tuple.hpp>
#include <boost/fusion/adapted/std_pair.hpp>

#include <gmp.h>

namespace metaSMT {

  // forward declare stack api
  struct stack_pop;
  struct stack_push;
  namespace features {
    struct stack_api;
  } // features

  namespace solver {
    namespace predtags = ::metaSMT::logic::tag;
    namespace bvtags = ::metaSMT::logic::QF_BV::tag;
    namespace arraytags = ::metaSMT::logic::Array::tag;
    namespace uftags = ::metaSMT::logic::QF_UF::tag;

    namespace qi = boost::spirit::qi;

    namespace detail {
      struct dummy {
        dummy() {}
      }; // dummy

      struct equals : boost::static_visitor<bool> {
        equals() {}

        template < typename T1, typename T2 >
        bool operator() (T1 const &, T2 const &) const {
          return false;
        }

        bool operator() (dummy const &, dummy const &) const {
          return true;
        }

        bool operator() (z3::func_decl const &lhs, z3::func_decl const &rhs) const {
          return eq(lhs, rhs);
        }

        bool operator() (z3::expr const &lhs, z3::expr const &rhs) const {
          return eq(lhs, rhs);
        }
      }; // equals

      struct domain_sort_visitor : boost::static_visitor<Z3_sort> {
        domain_sort_visitor(Z3_context &ctx)
          : ctx(ctx)
        {}

        Z3_sort operator() (type::Boolean const &arg) const {
          return Z3_mk_bool_sort(ctx);
        }

        Z3_sort operator() (type::BitVector const &arg) const {
          return Z3_mk_bv_sort(ctx, arg.width);
        }

        Z3_sort operator() (type::Array const &arg) const {
          Z3_sort index_type = Z3_mk_bv_sort(ctx, arg.index_width);
          Z3_sort elem_type = Z3_mk_bv_sort(ctx, arg.elem_width);
          return Z3_mk_array_sort(ctx, index_type, elem_type);
        }

        Z3_context &ctx;
      }; // domain_sort_visitor
    } // detail

    class Z3_Backend {
    public:
      struct result_type {
        // first type in variant has to be default constructable
        boost::variant<
          detail::dummy
        , z3::func_decl
        , z3::expr
        > internal;

        result_type() {}

        result_type(z3::expr a)
          : internal(a)
        {}

        result_type(z3::func_decl a)
          : internal(a)
        {}

        inline operator z3::expr() const {
          return boost::get<z3::expr>(internal);
        }

        inline operator z3::func_decl() const {
          return boost::get<z3::func_decl>(internal);
        }

        inline bool operator ==(result_type const &r) const {
          return boost::apply_visitor(detail::equals(), internal, r.internal);
        }

        inline bool operator !=(result_type const &r) const {
          return !operator ==(r);
        }
#if 0
        inline bool operator <(result_type const &r) const {
          assert( false && "Yet not implemented" );
          return false;
        }
#endif
      }; // result_type

      // typedef z3::ast result_type;

      Z3_Backend()
        : solver_(ctx_)
        , assumption_( (*this)(predtags::true_tag(), boost::any()) )
      {}

      ~Z3_Backend()
      {}

      result_wrapper read_value(result_type const &var) {
        z3::model model = solver_.get_model();
        std::string str;
        result_type r = model.eval(z3::expr(var), /* completion = */true);
        str = Z3_ast_to_string(ctx_, z3::expr(r));

        // predicate
        if ( str == "false" ) {
          return result_wrapper( false );
        }
        else if ( str == "true" ) {
          return result_wrapper( true );
        }

        // bit-vector
        typedef std::string::const_iterator ConstIterator;
        static qi::rule< ConstIterator, unsigned long() > binary_rule
          = qi::lit("#b") >> qi::uint_parser<unsigned long, 2, 1, -1>()
          ;

        static qi::rule< ConstIterator, unsigned long() > hex_rule
          = qi::lit("#x") >> qi::uint_parser<unsigned long, 16, 1, -1>()
          ;

        unsigned long value;
        ConstIterator it = str.begin(), ie = str.end();
        if ( qi::parse(it, ie, binary_rule, value) ) {
          // std::cout << str << '\n';
          // std::cout << std::string(it, ie) << "\n----\n";
          // std::cout.flush();
          assert( it == ie && "Expression not completely consumed" );
          unsigned const width = str.size() - 2;
          return result_wrapper( value, width );
        }

        it = str.begin(), ie = str.end();
        if ( qi::parse(it, ie, hex_rule, value) ) {
          // std::cout << str << '\n';
          // std::cout << std::string(it, ie) << "\n----\n";
          // std::cout.flush();
          assert( it == ie && "Expression not completely consumed" );
          unsigned const width = (str.size() - 2)*4;
          return result_wrapper( value, width );
        }

        // XXX: determinate size?
        // return result_wrapper(boost::logic::indeterminate);
        return result_wrapper(false);
      }

      void assertion( result_type const &e ) {
        solver_.add( static_cast<z3::expr const &>(e) );
      }

      void assumption( result_type const &e ) {
        assumption_ = (*this)(predtags::and_tag(), assumption_, e);
      }

      bool solve() {
        solver_.push();
        assertion(assumption_);
        z3::check_result result = solver_.check(ctx_);
        // std::cerr << result << '\n';
        solver_.pop();
        assumption_ = (*this)(predtags::true_tag(), boost::any());
        return (result == z3::sat);
      }

      result_type operator() (predtags::var_tag const & var, boost::any args) {
        char buf[64];
        sprintf(buf, "var_%u", var.id);
        return ctx_.bool_const(buf);
      }

      result_type operator() (bvtags::var_tag const & var, boost::any args) {
        char buf[64];
        sprintf(buf, "var_%u", var.id);
        return ctx_.bv_const(buf, var.width);
      }

      result_type operator() (arraytags::array_var_tag const &var,
                              boost::any const & ) {
        if (var.id == 0 ) {
          throw std::runtime_error("uninitialized array used");
        }

        z3::sort index_sort = ctx_.bv_sort(var.index_width);
        z3::sort elem_sort = ctx_.bv_sort(var.elem_width);
        z3::sort ty = ctx_.array_sort(index_sort, elem_sort);

        char buf[64];
        sprintf(buf, "var_%u", var.id);

        Z3_symbol s = Z3_mk_string_symbol(ctx_, buf);
        return z3::to_expr(ctx_, Z3_mk_const(ctx_, s, ty));
      }

        result_type operator() (uftags::function_var_tag const & var,
                                boost::any args) {
        unsigned const num_args = var.args.size();

        // construct the name of the uninterpreted_function
        char buf[64];
        sprintf(buf, "function_var_%u", var.id);

        Z3_symbol sym = ctx_.str_symbol(buf);

        // construct result sort
        Z3_context ctx = ctx_;
        Z3_sort result_sort = boost::apply_visitor(
          detail::domain_sort_visitor(ctx), var.result_type);

        // construct argument sorts
        Z3_sort *domain_sort = new Z3_sort[num_args];
        for ( unsigned u = 0; u < num_args; ++u ) {
          domain_sort[u] = boost::apply_visitor(
            detail::domain_sort_visitor(ctx), var.args[u]);
        }

        return z3::to_func_decl(ctx_,
          Z3_mk_func_decl(ctx_, sym, num_args, domain_sort, result_sort));
      }

      result_type operator() (proto::tag::function,
                              result_type const &func_decl) {
        Z3_ast *arg_array = 0;
        return z3::to_expr(ctx_,
          Z3_mk_app(ctx_, z3::func_decl(func_decl), 0, arg_array));
      }

      result_type operator() (proto::tag::function,
                              result_type func_decl,
                              result_type arg) {
        Z3_ast arg_array[] = { z3::expr(arg) };
        return z3::to_expr(ctx_,
          Z3_mk_app(ctx_, z3::func_decl(func_decl), 1, arg_array));
      }

      result_type operator() (proto::tag::function,
                              result_type func_decl,
                              result_type arg1,
                              result_type arg2) {
        Z3_ast arg_array[] = { z3::expr(arg1), z3::expr(arg2) };
        return z3::to_expr(ctx_,
          Z3_mk_app(ctx_, z3::func_decl(func_decl), 2, arg_array));
      }

      result_type operator() (proto::tag::function,
                              result_type func_decl,
                              result_type arg1,
                              result_type arg2,
                              result_type arg3) {
        Z3_ast arg_array[] = { z3::expr(arg1), z3::expr(arg2), z3::expr(arg3) };
        return z3::to_expr(ctx_,
          Z3_mk_app(ctx_, z3::func_decl(func_decl), 3, arg_array));
      }

      result_type operator() (predtags::false_tag const &, boost::any arg) {
        return ctx_.bool_val(false);
      }

      result_type operator() (predtags::true_tag const &, boost::any arg) {
        return ctx_.bool_val(true);
      }

      result_type operator() (predtags::not_tag const &, result_type const &a) {
        return !static_cast<z3::expr const &>( a );
      }

      result_type operator() (predtags::nand_tag const &,
                              result_type const &a, result_type const &b) {
        return (*this)(predtags::not_tag(),
                       (*this)(predtags::and_tag(), a, b) );
      }

      result_type operator() (predtags::nor_tag const &,
                              result_type const &a, result_type const &b) {
        return (*this)(predtags::not_tag(),
                       (*this)(predtags::or_tag(), a, b) );
      }

      result_type operator() (predtags::xnor_tag const &,
                              result_type const &a, result_type const &b) {
        return (*this)(predtags::not_tag(),
                       (*this)(predtags::xor_tag(), a, b) );
      }

      result_type operator() (predtags::ite_tag ,
                              result_type const &a,
                              result_type const &b,
                              result_type const &c) {
        return z3::to_expr(ctx_,
          Z3_mk_ite(ctx_, z3::expr(a), z3::expr(b), z3::expr(c)));
      }

      result_type operator() (bvtags::bit0_tag , boost::any arg) {
        return ctx_.bv_val(0, 1);
      }

      result_type operator() (bvtags::bit1_tag , boost::any arg) {
        return ctx_.bv_val(1, 1);
      }

      result_type operator() (bvtags::bvuint_tag const &, boost::any const &arg) {
        typedef boost::tuple<unsigned long, unsigned long> P;
        P const p = boost::any_cast<P>(arg);
        unsigned long const value = boost::get<0>(p);
        unsigned const width = boost::get<1>(p);
        Z3_sort ty = Z3_mk_bv_sort(ctx_, width);
        return z3::to_expr(ctx_, Z3_mk_unsigned_int64(ctx_, value, ty));
      }

      result_type operator() (bvtags::bvsint_tag const &, boost::any const &arg) {
        typedef boost::tuple<long, unsigned long> P;
        P const p = boost::any_cast<P>(arg);
        long const value = boost::get<0>(p);
        unsigned const width = boost::get<1>(p);
        Z3_sort ty = Z3_mk_bv_sort(ctx_, width);
        return z3::to_expr(ctx_, Z3_mk_int64(ctx_, value, ty));
      }

      result_type operator() (bvtags::bvbin_tag , boost::any arg) {
        std::string s = boost::any_cast<std::string>(arg);
        size_t const len = s.size();
        mpz_t value;
        mpz_init(value);
        mpz_set_str(value, s.c_str(), 2);
        std::string int_string( mpz_get_str(NULL, 10, value) );
        result_type r = ctx_.bv_val(int_string.c_str(), len);
        mpz_clear(value);
        return r;
      }

      // XXX will be removed in a later revision
      result_type operator() (bvtags::bvhex_tag , boost::any arg) {
        std::string const hex = boost::any_cast<std::string>(arg);
        std::string bin (hex.size()*4,'\0');

        for (unsigned i = 0; i < hex.size(); ++i) {
          switch ( tolower(hex[i]) ) {
          case '0':
            bin.replace(4*i,4, "0000");
            break;
          case '1':
            bin.replace(4*i,4, "0001");
            break;
          case '2':
            bin.replace(4*i,4, "0010");
            break;
          case '3':
            bin.replace(4*i,4, "0011");
            break;
          case '4':
            bin.replace(4*i,4, "0100");
            break;
          case '5':
            bin.replace(4*i,4, "0101");
            break;
          case '6':
            bin.replace(4*i,4, "0110");
            break;
          case '7':
            bin.replace(4*i,4, "0111");
            break;
          case '8':
            bin.replace(4*i,4, "1000");
            break;
          case '9':
            bin.replace(4*i,4, "1001");
            break;
          case 'a':
            bin.replace(4*i,4, "1010");
            break;
          case 'b':
            bin.replace(4*i,4, "1011");
            break;
          case 'c':
            bin.replace(4*i,4, "1100");
            break;
          case 'd':
            bin.replace(4*i,4, "1101");
            break;
          case 'e':
            bin.replace(4*i,4, "1110");
            break;
          case 'f':
            bin.replace(4*i,4, "1111");
            break;
          }
        }
        // std::cout << bin << std::endl;
        return (*this)(bvtags::bvbin_tag(), boost::any(bin));
      }

      result_type operator() (bvtags::bvcomp_tag,
                              result_type const &a,
                              result_type const &b) {
        result_type bit1 = (*this)(bvtags::bit1_tag(), boost::any());
        result_type bit0 = (*this)(bvtags::bit0_tag(), boost::any());
        return z3::to_expr(ctx_,
          Z3_mk_ite(ctx_, Z3_mk_eq(ctx_, z3::expr(a), z3::expr(b)),
                    z3::expr(bit1), z3::expr(bit0)));
      }

      result_type operator() (bvtags::extract_tag const &,
                              unsigned long upper,
                              unsigned long lower,
                              result_type const &e) {
        return z3::to_expr(ctx_,
          Z3_mk_extract(ctx_, upper, lower, z3::expr(e)));
      }

      result_type operator() (bvtags::zero_extend_tag const &,
                              unsigned long width,
                              result_type e) {
        return z3::to_expr(ctx_, Z3_mk_zero_ext(ctx_, width, z3::expr(e)));
      }

      result_type operator() (bvtags::sign_extend_tag const &, 
                              unsigned long width,
                              result_type e) {
        return z3::to_expr(ctx_, Z3_mk_sign_ext(ctx_, width, z3::expr(e)));
      }

      result_type operator() (arraytags::select_tag const &
                              , result_type const &array
                              , result_type const &index) {
        return z3::select(z3::expr(array),
                          z3::expr(index));
      }

      result_type operator() (arraytags::store_tag const &
                              , result_type const &array
                              , result_type const &index
                              , result_type const &value) {
        return z3::store(z3::expr(array),
                         z3::expr(index),
                         z3::expr(value));
      }

      template< Z3_ast (*FN) (Z3_context, Z3_ast) >
      struct Z3_F1 {
        static Z3_ast exec(Z3_context c, Z3_ast x) {
          return (*FN)(c, x);
        }
      }; // Z3_F1

      template <typename TagT>
      result_type operator() (TagT tag, result_type a) {
        namespace mpl = boost::mpl;

        typedef mpl::map<
          mpl::pair<predtags::not_tag,      Z3_F1<&Z3_mk_not> >
        , mpl::pair<bvtags::bvneg_tag,      Z3_F1<&Z3_mk_bvneg> >
        , mpl::pair<bvtags::bvnot_tag,      Z3_F1<&Z3_mk_bvnot> >
        > UnaryOpcodeMap;

        typedef
          typename mpl::has_key< UnaryOpcodeMap, TagT >::type
          _has_key;
        if  ( _has_key::value ) {
          typedef typename mpl::eval_if<
          _has_key
          , mpl::at< UnaryOpcodeMap, TagT >
          , mpl::identity< Z3_F1<Z3_mk_not> >
          >::type opcode;
          Z3_ast r = opcode::exec(ctx_, z3::expr(a));
          z3::expr(a).check_error();
          return z3::expr(z3::expr(a).ctx(), r);
        } else {
          std::cout << "unknown operator: " << tag << std::endl;
          assert(false && "unknown operator");
          return (*this)(predtags::false_tag(), boost::any());
        }
      }

      template< Z3_ast (*FN) (Z3_context, Z3_ast, Z3_ast) >
      struct Z3_F2 {
        static Z3_ast exec(Z3_context c, Z3_ast x, Z3_ast y) {
          return (*FN)(c, x, y);
        }
      }; // Z3_F2

      template< Z3_ast (*FN) (Z3_context, unsigned, Z3_ast const []) >
      struct Z3_F2_MULTI_ARG {
        static Z3_ast exec(Z3_context c, Z3_ast x, Z3_ast y) {
          Z3_ast args[2] = { x, y };
          return (*FN)(c, 2, args);
        }
      }; // Z3_F2_MULTI_ARG

      template <typename TagT>
      result_type operator() (TagT tag, result_type a, result_type b) {
        namespace mpl = boost::mpl;
        typedef mpl::map31<
          mpl::pair<bvtags::bvand_tag,      Z3_F2<&Z3_mk_bvand> >
        , mpl::pair<bvtags::bvnand_tag,     Z3_F2<&Z3_mk_bvnand> >
        , mpl::pair<bvtags::bvor_tag,       Z3_F2<&Z3_mk_bvor> >
        , mpl::pair<bvtags::bvxor_tag,      Z3_F2<&Z3_mk_bvxor> >
        , mpl::pair<bvtags::bvnor_tag,      Z3_F2<&Z3_mk_bvnor> >
        , mpl::pair<bvtags::bvxnor_tag,     Z3_F2<&Z3_mk_bvxnor> >
        , mpl::pair<bvtags::bvsub_tag,      Z3_F2<&Z3_mk_bvsub> >
        , mpl::pair<bvtags::bvadd_tag,      Z3_F2<&Z3_mk_bvadd> >
        , mpl::pair<bvtags::bvmul_tag,      Z3_F2<&Z3_mk_bvmul> >
        , mpl::pair<bvtags::bvsle_tag,      Z3_F2<&Z3_mk_bvsle> >
        // #10
        , mpl::pair<bvtags::bvslt_tag,      Z3_F2<&Z3_mk_bvslt> >
        , mpl::pair<bvtags::bvsge_tag,      Z3_F2<&Z3_mk_bvsge> >
        , mpl::pair<bvtags::bvsgt_tag,      Z3_F2<&Z3_mk_bvsgt> >
        , mpl::pair<bvtags::bvule_tag,      Z3_F2<&Z3_mk_bvule> >
        , mpl::pair<bvtags::bvult_tag,      Z3_F2<&Z3_mk_bvult> >
        , mpl::pair<bvtags::bvuge_tag,      Z3_F2<&Z3_mk_bvuge> >
        , mpl::pair<bvtags::bvugt_tag,      Z3_F2<&Z3_mk_bvugt> >
        , mpl::pair<predtags::implies_tag,  Z3_F2<&Z3_mk_implies> >
        , mpl::pair<predtags::xor_tag,      Z3_F2<&Z3_mk_xor> >
        , mpl::pair<predtags::and_tag,      Z3_F2_MULTI_ARG<&Z3_mk_and> >
        // #20
        , mpl::pair<predtags::or_tag,       Z3_F2_MULTI_ARG<&Z3_mk_or> >
        , mpl::pair<predtags::equal_tag,    Z3_F2<&Z3_mk_eq> >
        , mpl::pair<predtags::nequal_tag,   Z3_F2_MULTI_ARG<&Z3_mk_distinct> >
        , mpl::pair<bvtags::concat_tag,     Z3_F2<&Z3_mk_concat> >
        , mpl::pair<bvtags::bvudiv_tag,     Z3_F2<&Z3_mk_bvudiv> >
        , mpl::pair<bvtags::bvurem_tag,     Z3_F2<&Z3_mk_bvurem> >
        , mpl::pair<bvtags::bvsdiv_tag,     Z3_F2<&Z3_mk_bvsdiv> >
        , mpl::pair<bvtags::bvsrem_tag,     Z3_F2<&Z3_mk_bvsrem> >
        , mpl::pair<bvtags::bvshl_tag,      Z3_F2<&Z3_mk_bvshl> >
        , mpl::pair<bvtags::bvshr_tag,      Z3_F2<&Z3_mk_bvlshr> >
        // #30
        , mpl::pair<bvtags::bvashr_tag,     Z3_F2<&Z3_mk_bvashr> >
        > BinaryOpcodeMap;

        typedef
          typename mpl::has_key< BinaryOpcodeMap, TagT >::type
          _has_key;
        if ( _has_key::value ) {
          typedef typename mpl::eval_if<
            _has_key
          , mpl::at< BinaryOpcodeMap, TagT >
          , mpl::identity< Z3_F2<Z3_mk_implies> >
          >::type opcode;
          Z3_ast r = opcode::exec(ctx_, z3::expr(a), z3::expr(b));
          z3::expr(a).check_error();
          return z3::expr(z3::expr(a).ctx(), r);
        } else {
          std::cout << "unknown operator: " << tag << std::endl;
          assert(false && "unknown operator");
          return (*this)(predtags::false_tag(), boost::any());
        }
      }

      ////////////////////////
      // Fallback operators //
      ////////////////////////
      template < typename Tag, typename T >
      result_type operator() ( Tag const &, T const & ) {
        assert( false );
        throw std::exception();
      }

      template < typename Tag, typename T1, typename T2 >
      result_type operator() ( Tag const &, T1 const &, T2 const & ) {
        assert( false );
        throw std::exception();
      }

      template < typename Tag, typename T1, typename T2, typename T3 >
      result_type operator() ( Tag const &, T1 const &, T2 const &, T3 const & ) {
        assert( false );
        throw std::exception();
      }

      void command( stack_push const &, unsigned howmany ) {
        while (howmany > 0) {
          solver_.push();
          --howmany;
        }
      }

      void command( stack_pop const &, unsigned howmany ) {
        solver_.pop(howmany);
      }

    private:
      z3::context ctx_;
      z3::solver solver_;
      result_type assumption_;
    }; // Z3_Backend
  } // solver

  namespace features {
    template<>
    struct supports< solver::Z3_Backend, features::stack_api >
    : boost::mpl::true_ {};
  } // features
} // metaSMT
