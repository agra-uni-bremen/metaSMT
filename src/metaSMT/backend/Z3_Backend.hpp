#pragma once

#include "../tags/QF_BV.hpp"
#include "../tags/QF_UF.hpp"
#include "../tags/Array.hpp"
#include "../result_wrapper.hpp"
#include "../Features.hpp"

extern "C" {
#include <z3.h>
}

#include <iostream>
#include <string>
#include <map>
#include <limits>
#include <boost/mpl/map.hpp>
#include <boost/mpl/map/map40.hpp>
#include <boost/dynamic_bitset.hpp>
#include <boost/any.hpp>

#include <boost/spirit/include/qi.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_io.hpp>
#include <boost/fusion/adapted/boost_tuple.hpp>
#include <boost/fusion/adapted/std_pair.hpp>
// #include <boost/spirit/debug.hpp>

namespace metaSMT {

  // forward declare stack api
  struct stack_pop;
  struct stack_push;
  namespace features {
    struct stack_api;
  } /* features */


  namespace solver {

    namespace predtags = ::metaSMT::logic::tag;
    namespace bvtags = ::metaSMT::logic::QF_BV::tag;
    namespace arraytags = ::metaSMT::logic::Array::tag;
    namespace uftags = ::metaSMT::logic::QF_UF::tag;
    namespace qi = boost::spirit::qi;
    namespace ascii = boost::spirit::ascii;

    struct domain_type_visitor : boost::static_visitor<Z3_sort> {
      domain_type_visitor(Z3_context &z3)
        : z3_(z3)
      {}

      Z3_sort operator() (type::BitVector const &arg) const {
        return Z3_mk_bv_sort(z3_, arg.width);
      }

      Z3_sort operator() (type::Boolean const &arg) const {
        return Z3_mk_bool_sort(z3_);
      }

      Z3_sort operator() (type::Array const &arg) const {
        Z3_sort index_type = Z3_mk_bv_sort(z3_, arg.index_width);
        Z3_sort elem_type = Z3_mk_bv_sort(z3_, arg.elem_width);
        return Z3_mk_array_sort(z3_, index_type, elem_type);
      }

      Z3_context &z3_;
    }; // domain_type_visitor

    /**
     * \ingroup Backend
     * \class Z3_Backend Z3_Backend.hpp metaSMT/backend/Z3_Backend.hpp
     *
     * \brief Backend for the Z3 SMT solver
     **/
    class Z3_Backend {
    public:
      struct result_type {
        boost::variant<Z3_ast, Z3_func_decl> internal;

        result_type()
        {}

        result_type(Z3_ast a)
          : internal(a)
        {}

        result_type(Z3_func_decl a)
          : internal(a)
        {}

        inline operator Z3_ast() const {
          return boost::get<Z3_ast>(internal);
        }

        inline operator Z3_func_decl() const {
          return boost::get<Z3_func_decl>(internal);
        }

        inline bool operator ==(result_type const &r) const {
          return (internal == r.internal);
        }

        inline bool operator !=(result_type const &r) const {
          return !(internal == r.internal);
        }

        inline bool operator <(result_type const &r) const {
          return (internal < r.internal);
        }
      };
      // typedef Z3_ast result_type;

      Z3_Backend () {
        Z3_config cfg;
        cfg = Z3_mk_config();
        z3_ = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        m_ = 0;
        assumption_ = (*this)(predtags::true_tag(), boost::any());
      }

      ~Z3_Backend() {
        if (m_) {
          Z3_del_model(z3_, m_);
          m_ = 0;
        }
        if (z3_) {
          Z3_del_context(z3_);
          z3_ = 0;
        }
      }

      void assertion( result_type e ) {
        Z3_assert_cnstr(z3_, e);
      }

      void assumption( result_type e ) {
        Z3_ast args[2] = { assumption_, e };
        assumption_ = Z3_mk_and(z3_, 2, args);
      }

      void command ( stack_push const &, unsigned howmany) {
        while (howmany > 0) {
          Z3_push(z3_);
          --howmany;
        }
      }

      void command ( stack_pop const &, unsigned howmany) {
        Z3_pop(z3_, howmany);
      }

      bool solve() {
        if (m_) {
          Z3_del_model(z3_, m_);
          m_ = 0;
          model_map_.clear();
        }
        Z3_push(z3_);
        assertion(assumption_);
        Z3_lbool sat = Z3_check_and_get_model(z3_, &m_);
        Z3_pop(z3_, 1);
        assumption_ = (*this)(predtags::true_tag(), boost::any());
        // Z3_trace_to_file(z3_, "z3_trace_log.txt");
        return (sat == Z3_L_TRUE);
      }

      result_wrapper read_value(result_type var) {
        if (model_map_.empty()) {
          std::string model_str = Z3_model_to_string(z3_, m_);
          // std::cout << model_str << '\n';
          build_model_map(model_str);
        }
        std::string var_name = Z3_ast_to_string(z3_, var);

        model_map::const_iterator it = model_map_.find(var_name);
        if (it != model_map_.end()) {

          unsigned long value = it->second.get<0>();
          unsigned long width = it->second.get<1>();

          //std::cout << "read_value: " << value << ' ' << width << std::endl;

          if (width == 0) {
            return result_wrapper(value == 1);
          }

          return result_wrapper(value, width);
        }

        // XXX: determinate size?
        // return result_wrapper(boost::logic::indeterminate);
        return result_wrapper(false);
      }

      result_type operator() (predtags::false_tag , boost::any arg) {
        return Z3_mk_false(z3_);
      }

      result_type operator() (predtags::true_tag , boost::any arg) {
        return Z3_mk_true(z3_);
      }

      result_type operator() (predtags::nor_tag ,
                              result_type a,
                              result_type b) {
        Z3_ast args[2] = { a, b };
        return Z3_mk_not(z3_, Z3_mk_or(z3_, 2, args));
      }

      result_type operator() (predtags::nand_tag ,
                              result_type a,
                              result_type b) {
        Z3_ast args[2] = { a, b };
        return Z3_mk_not(z3_, Z3_mk_and(z3_, 2, args));
      }

      result_type operator() (predtags::xnor_tag ,
                              result_type a,
                              result_type b) {
        return Z3_mk_not(z3_, Z3_mk_xor(z3_, a, b));
      }

      result_type operator() (predtags::ite_tag ,
                              result_type a,
                              result_type b,
                              result_type c) {
        return Z3_mk_ite(z3_, a, b, c);
      }

      result_type operator() (predtags::var_tag const & var, boost::any args) {
        Z3_sort ty = Z3_mk_bool_sort(z3_);
        char buf[64];
        sprintf(buf, "var_%u", var.id);
        Z3_symbol s = Z3_mk_string_symbol(z3_, buf);
        return Z3_mk_const(z3_, s, ty);
      }

      result_type operator() (uftags::function_var_tag const & var, boost::any args) {
        unsigned const num_args = var.args.size();

        // construct the name of the uninterpreted_function
        char buf[64];
        sprintf(buf, "function_var_%u", var.id);
        Z3_symbol uf_name = Z3_mk_string_symbol(z3_, buf);

        // construct result sort
        sprintf(buf, "return_type_%u", var.id);
        //Z3_symbol result_name = Z3_mk_string_symbol(z3_, buf);
        Z3_sort result_type = boost::apply_visitor(domain_type_visitor(z3_), var.result_type);

        // construct argument sorts
        Z3_sort *domain_type = new Z3_sort[num_args];
        for (unsigned u = 0; u < num_args; ++u) {
          sprintf(buf, "domain_%u_%u", var.id, u);
          //Z3_symbol dom_name = Z3_mk_string_symbol(z3_, buf);
          domain_type[u] = boost::apply_visitor(domain_type_visitor(z3_), var.args[u]);
        }

        Z3_func_decl uf = Z3_mk_func_decl(z3_, uf_name, num_args, domain_type, result_type);
        return uf;
      }

      result_type operator() (proto::tag::function,
                              result_type func_decl) {
        Z3_ast *arg_array = 0;
        return Z3_mk_app(z3_, func_decl, 0, arg_array);
      }

      result_type operator() (proto::tag::function,
                              result_type func_decl,
                              result_type arg) {
        Z3_ast arg_array[] = { arg };
        return Z3_mk_app(z3_, func_decl, 1, arg_array);
      }

      result_type operator() (proto::tag::function,
                              result_type func_decl,
                              result_type arg1,
                              result_type arg2) {
        Z3_ast arg_array[] = { arg1, arg2 };
        return Z3_mk_app(z3_, func_decl, 2, arg_array);
      }

      result_type operator() (proto::tag::function,
                              result_type func_decl,
                              result_type arg1,
                              result_type arg2,
                              result_type arg3) {
        Z3_ast arg_array[] = { arg1, arg2, arg3 };
        return Z3_mk_app(z3_, func_decl, 3, arg_array);
      }

      result_type operator() (bvtags::bvcomp_tag ,
                              result_type a,
                              result_type b) {
        return Z3_mk_ite(z3_, Z3_mk_eq(z3_, a, b),
                         (*this)(bvtags::bit1_tag(), boost::any()),
                         (*this)(bvtags::bit0_tag(), boost::any()));
      }

      result_type operator() (bvtags::extract_tag const &,
                              unsigned long upper, unsigned long lower,
                              result_type e) {
        return Z3_mk_extract(z3_, upper, lower, e);
      }

        result_type operator() (bvtags::zero_extend_tag const & 
            , unsigned long width
            , result_type e)
        {
          return Z3_mk_zero_ext(z3_, width, e);
        }

        result_type operator() (bvtags::sign_extend_tag const & 
            , unsigned long width
            , result_type e)
        {
          return Z3_mk_sign_ext(z3_, width, e);
        }

      result_type operator() (bvtags::var_tag const & var, boost::any args) {
        Z3_sort ty = Z3_mk_bv_sort(z3_, var.width);
        char buf[64];
        sprintf(buf, "var_%u", var.id);
        Z3_symbol s = Z3_mk_string_symbol(z3_, buf);
        return Z3_mk_const(z3_, s, ty);
      }

      result_type operator() (bvtags::bit0_tag , boost::any arg) {
        Z3_sort ty = Z3_mk_bv_sort(z3_, 1);
        return Z3_mk_unsigned_int(z3_, 0, ty);
      }

      result_type operator() (bvtags::bit1_tag , boost::any arg) {
        Z3_sort ty = Z3_mk_bv_sort(z3_, 1);
        return Z3_mk_unsigned_int(z3_, 1, ty);
      }

      result_type operator() (bvtags::bvuint_tag , boost::any arg) {
        const size_t ubits = std::numeric_limits<unsigned>::digits;

        typedef boost::tuple<unsigned long, unsigned long> P;
        P p = boost::any_cast<P>(arg);
        unsigned long const value = boost::get<0>(p);
        unsigned const width = boost::get<1>(p);

        if( value <= std::numeric_limits<unsigned int>::max() || width <= ubits ) {
          Z3_sort ty = Z3_mk_bv_sort(z3_, width);
          return Z3_mk_unsigned_int(z3_, value, ty);
        } else {
          const unsigned part1 = static_cast<unsigned>(value);
          const unsigned part2 = static_cast<unsigned>(value>>ubits);
          Z3_sort ty1 = Z3_mk_bv_sort(z3_, ubits);
          Z3_sort ty2 = Z3_mk_bv_sort(z3_, width-ubits);
          return Z3_mk_concat(z3_,
            Z3_mk_unsigned_int(z3_, part2, ty2),
            Z3_mk_unsigned_int(z3_, part1, ty1)
          );
        }
      }

      result_type operator() (bvtags::bvsint_tag , boost::any arg) {
        const size_t ibits = std::numeric_limits<int>::digits;

        typedef boost::tuple<long, unsigned long> P;
        P p = boost::any_cast<P>(arg);
        long const value = boost::get<0>(p);
        unsigned const width = boost::get<1>(p);

        if( (value <= std::numeric_limits<int>::max() && value >= std::numeric_limits<int>::min()) || width <= ibits ) {
          Z3_sort ty = Z3_mk_bv_sort(z3_, width);
          return Z3_mk_int(z3_, value, ty);
        } else {
          const int part1 = static_cast<int>(value);
          const int part2 = static_cast<int>(value<<ibits);
          //std::cout << "signed multipart: " << part2 << " | " << part1 << std::endl;
          Z3_sort ty1 = Z3_mk_bv_sort(z3_, ibits);
          Z3_sort ty2 = Z3_mk_bv_sort(z3_, width-ibits);
          return Z3_mk_concat(z3_,
            Z3_mk_int(z3_, part2, ty2),
            Z3_mk_int(z3_, part1, ty1)
          );
        }
      }

      result_type operator() (bvtags::bvbin_tag , boost::any arg) {
        const size_t ubits = std::numeric_limits<unsigned>::digits;
        std::string s = boost::any_cast<std::string>(arg);
        const size_t len = s.size();
        bool first = true;
        result_type result;
        for (unsigned i = 0; i < len; i+=ubits) {
          //std::cout << i << "-" << (i+ubits) << ": " << s.substr(i, ubits) << std::endl;
          unsigned part = boost::dynamic_bitset<>(s, i, ubits).to_ulong();
          //std::cout << "part " << i << '-' << (i+std::min( len-i, ubits)) << ": " << part << std::endl;
          Z3_sort ty = Z3_mk_bv_sort(z3_, std::min( len-i, ubits));
          if (first) {
            result = Z3_mk_unsigned_int(z3_, part, ty);
            first = false;
          } else {
            result = Z3_mk_concat(z3_, result, Z3_mk_unsigned_int(z3_, part, ty) );
          }
        }
        return result;
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
        ////std::cout << bin << std::endl;
        return (*this)(bvtags::bvbin_tag(), bin);
      }

      result_type operator() (arraytags::array_var_tag const & var, boost::any const & ) 
      {
        if(var.id == 0 ) {
          throw std::runtime_error("uninitialized array used");
        }
        Z3_sort indexT = Z3_mk_bv_sort(z3_, var.index_width );
        Z3_sort elemT  = Z3_mk_bv_sort(z3_, var.elem_width );

        Z3_sort ty = Z3_mk_array_sort(z3_, indexT, elemT);

        char buf[64];
        sprintf(buf, "var_%u", var.id);
        Z3_symbol s = Z3_mk_string_symbol(z3_, buf);
        return  Z3_mk_const(z3_, s, ty);
      }

      result_type operator() (arraytags::select_tag const &
                              , result_type array
                              , result_type index) {
        //return boolector_read(_btor, array, index);
        return Z3_mk_select(z3_, array, index);
      }

      result_type operator() (arraytags::store_tag const &
                              , result_type array
                              , result_type index
                              , result_type value) {
        //return boolector_write(_btor, array, index, value);
        return Z3_mk_store(z3_, array, index, value);
      }

      ////////////////////////
      // Fallback operators //
      ////////////////////////

      template <typename TagT>
      result_type operator() (TagT tag, boost::any args ) {
        return (*this)(predtags::false_tag(), boost::any());
      }

      template< Z3_ast (*FN) (Z3_context, Z3_ast) >
      struct Z3_F1 {
        static Z3_ast exec(Z3_context c, Z3_ast x) {
          return (*FN)(c, x);
        }
      };

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
          return opcode::exec(z3_, a);
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
      };

      template< Z3_ast (*FN) (Z3_context, unsigned, Z3_ast const []) >
      struct Z3_F2_MULTI_ARG {
        static Z3_ast exec(Z3_context c, Z3_ast x, Z3_ast y) {
          Z3_ast args[2] = { x, y };
          return (*FN)(c, 2, args);
        }
      };

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

        , mpl::pair<bvtags::bvashr_tag,     Z3_F2<&Z3_mk_bvashr> >
        > BinaryOpcodeMap;

        typedef
          typename mpl::has_key< BinaryOpcodeMap, TagT >::type
          _has_key;
        if ( _has_key::value ) {
          typedef typename mpl::eval_if<
            _has_key
            , mpl::at< BinaryOpcodeMap, TagT >
            , mpl::identity< Z3_F2<Z3_mk_bvand> >
            >::type opcode;
          return opcode::exec(z3_, a, b);
        } else {
          std::cout << "unknown operator: " << tag << std::endl;
          assert(false && "unknown operator");
          return (*this)(predtags::false_tag(), boost::any());
        }
      }

      template <typename TagT, typename T1, typename T2, typename T3>
      result_type operator() (TagT tag, T1 a, T2 b, T3 c) {
        return (*this)(predtags::false_tag(), boost::any());
      }

    protected:
      typedef std::string::const_iterator ConstIterator;
      typedef boost::tuple<unsigned long, unsigned long> BitvectorTuple;
      typedef std::pair<std::string, BitvectorTuple> NamedTuple;

      void build_model_map(std::string const &assign_str) {
        ConstIterator it = assign_str.begin();
        ConstIterator ie = assign_str.end();

        static qi::rule<ConstIterator, std::string() > name_rule
          = +(qi::char_ - qi::char_(" ()"))
          ;

        static qi::rule<ConstIterator, BitvectorTuple() > true_rule
          = "true" >> qi::attr(1u) >> qi::attr(0u)
          ;

        static qi::rule<ConstIterator, BitvectorTuple() > false_rule
          = "false" >> qi::attr(0u) >> qi::attr(0u)
          ;

        static qi::rule<ConstIterator, BitvectorTuple() > bitvector_rule
          = "bv" >> qi::ulong_ >> '[' >> qi::ulong_ >> ']'
          ;
        static qi::rule<ConstIterator, BitvectorTuple() > value_rule
          = ( true_rule | false_rule | bitvector_rule );
          
        static qi::rule<ConstIterator, NamedTuple() > line_2_15
          = name_rule >> qi::lit(" -> ")  
            >> ( true_rule | false_rule | bitvector_rule ) 
          ;

        static qi::rule<ConstIterator, std::string()> sexpr
          = qi::raw[
            name_rule
          |    qi::lit("(")
            >> *qi::space
            >> *((sexpr) >> *qi::space)
            >> qi::lit(")")
          ];

        // tested with for 2.18 and 2.19
        static qi::rule<ConstIterator, NamedTuple() > line_2_18
          = qi::lit("(define ") >> name_rule >> qi::lit(" ")
            >> value_rule >> ')'
          ;
          ;

        static qi::rule<ConstIterator > array_2_18
          = qi::raw[
            qi::lit("(define ") >> name_rule
            >> " as-array[" >> *(~qi::char_(']')) >> "])"
          ];

        static qi::rule<ConstIterator > function_2_18
          = qi::raw[
            qi::lit("(define ") >> sexpr >> +qi::space >> sexpr>> qi::lit(')')
          ];

        static qi::rule<ConstIterator, model_map() > rule
          = *((
                line_2_18 
              | line_2_15
              | qi::omit[array_2_18]
              | qi::omit[function_2_18]
              //| sexpr
              ) >> -qi::eol )
          ;

        //rule.name("rule");
        //name_rule.name("name_rule");
        //true_rule.name("true_rule");
        //false_rule.name("false_rule");
        //bitvector_rule.name("bitvector_rule");
        //sexpr.name("sexpr");
        //line_2_15.name("line_2_15");
        //line_2_18.name("line_2_18");
        //array_2_18.name("array_2_18");
        //function_2_18.name("function_2_18");

        //debug(rule); // requires implementation of operator <<(.) for model_map
        //debug(name_rule);
        //debug(true_rule);
        //debug(false_rule);
        //debug(bitvector_rule);
        //debug(sexpr);
        //debug(line_2_15);
        //debug(line_2_18);
        //debug(array_2_18);
        //debug(function_2_18);

        if (qi::parse(it, ie, rule, model_map_)) {
          if (it != ie ) {
            //std::cout << assign_str << "\n----\n";
            //std::cout << std::string(it,ie) << "\n----\n";
            //std::cout.flush();
            assert( it == ie && "Expression not completely consumed" );
          }
          return;
        }

        assert(false && "Parsing failed");
      }

    private:
      typedef std::map<std::string, BitvectorTuple> model_map;
      model_map model_map_;

      Z3_context z3_;
      Z3_model m_;
      Z3_ast assumption_;
    };
  } // namespace solver

  namespace features {
    template<>
    struct supports< solver::Z3_Backend, features::stack_api>
    : boost::mpl::true_ {};
  } /* features */

} // namespace metaSMT

//  vim: ft=cpp:ts=2:sw=2:expandtab
