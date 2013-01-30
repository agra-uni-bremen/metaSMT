#pragma once

#include "../tags/QF_BV.hpp"
#include "../impl/_var_id.hpp"
#include "Logic.hpp"
#include "Array.hpp"
#include <boost/functional/hash.hpp>
#include <boost/proto/core.hpp>
#include <boost/type_traits/is_signed.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>
#include <string>


namespace proto = boost::proto;

namespace metaSMT {

  namespace logic {
    /**
     *  @brief SMT Qantifier Free Bit-Vector Theory
     *
     **/
    namespace QF_BV {

      struct QF_BV_Grammar;

      struct QF_BV_Unary_Function
        :proto::or_<
            proto::unary_expr<tag::bvnot_tag, QF_BV_Grammar>
          , proto::unary_expr<tag::bvneg_tag, QF_BV_Grammar>
         >
      {};

      struct QF_BV_Binary_Function
        : proto::or_<
          //logic
            proto::or_<
              proto::binary_expr<tag::bvand_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvnand_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvor_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvnor_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvxor_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvxnor_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvcomp_tag, QF_BV_Grammar, QF_BV_Grammar>
            >
          // arithmetic
          , proto::or_<
              proto::binary_expr<tag::bvadd_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvmul_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvsub_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvudiv_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvurem_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvsdiv_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvsrem_tag, QF_BV_Grammar, QF_BV_Grammar>
            >
          // extend
          , proto::or_<
              proto::binary_expr<tag::concat_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::extract_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::zero_extend_tag, QF_BV_Grammar, unsigned long>
            , proto::binary_expr<tag::sign_extend_tag, QF_BV_Grammar, unsigned long>
            >
          // shifting
          , proto::or_<
              proto::binary_expr<tag::bvshl_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvshr_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvashr_tag, QF_BV_Grammar, QF_BV_Grammar>
            >
          // Accept other expressions (e.g. array)
          , proto::_
        >
      {};

      struct QF_BV_Binary_Predicate
        : proto::or_<
          //comparison
            proto::or_<
              proto::binary_expr<tag::bvslt_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvsgt_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvsle_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvsge_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvult_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvugt_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvule_tag, QF_BV_Grammar, QF_BV_Grammar>
            , proto::binary_expr<tag::bvuge_tag, QF_BV_Grammar, QF_BV_Grammar>
            >
        >
      {};

      struct QF_BV_BitVector_Constant
        : proto::or_<
            proto::binary_expr < tag::bvuint_tag
              , proto::terminal< proto::convertible_to< unsigned long > >
              , proto::terminal< proto::convertible_to< unsigned long > >
            >
          , proto::binary_expr < tag::bvsint_tag
              , proto::terminal< proto::convertible_to<          long > >
              , proto::terminal< proto::convertible_to< unsigned long > >
            >
          , proto::unary_expr < tag::bvbin_tag
              , proto::terminal< proto::convertible_to< std::string > >
            >
          , proto::unary_expr < tag::bvhex_tag
              , proto::terminal< proto::convertible_to< std::string > >
            >
        >
      {};


      // real Grammar
      struct QF_BV_Grammar 
        : proto::and_<
            proto::not_< proto::address_of< proto::_ > >
	  , proto::not_< proto::equal_to< proto::_, proto::_ > >
	  , proto::or_<
              proto::terminal< tag::bit0_tag >
            , proto::terminal< tag::bit1_tag >
            , proto::terminal< tag::var_tag > 
            , QF_BV_BitVector_Constant
            , QF_BV_Binary_Function
            , QF_BV_Binary_Predicate
            , QF_BV_Unary_Function
	  > >
      {};

      template<typename Expr>
      struct QF_BV;

      struct QF_BV_Domain
      : proto::domain<proto::generator<QF_BV>, QF_BV_Grammar>
      {};

      template<typename Expr>
        struct QF_BV
        : proto::extends<Expr, QF_BV<Expr>, QF_BV_Domain >
        {
          typedef proto::extends<Expr, QF_BV<Expr>, QF_BV_Domain > base_type;

          QF_BV(Expr const & expr = Expr()) 
            : base_type(expr)
          {
          }
        };

      template<typename Expr> 
      void check (QF_BV<Expr> const & ) {
        BOOST_MPL_ASSERT((proto::matches<Expr, QF_BV_Grammar>));
      }
      template<typename Expr> 
      void check_not (QF_BV<Expr> const & ) {
        BOOST_MPL_ASSERT_NOT((proto::matches<Expr, QF_BV_Grammar>));
      }

      /** 
       * @defgroup QF_BV QF_BV (Bit-Vector) Frontend
       * @ingroup Frontend
       * @{
       */

      // expressions
      QF_BV<proto::terminal<tag::bit0_tag>::type  > const bit0; // = {{{}}};
      QF_BV<proto::terminal<tag::bit1_tag>::type  > const bit1; // = {{{}}};


 #define _QF_BV_BINARY_FUNCTION(NAME_, TAG_) \
      template<typename E1, typename E2> \
      typename proto::result_of::make_expr< TAG_, QF_BV_Domain, E1 const &, E2 const & >::type \
      NAME_( E1 const& e1, E2 const & e2 ) \
      { \
        return proto::make_expr< TAG_, QF_BV_Domain >(boost::cref(e1), boost::cref(e2));\
      } 

      // bitwise binary
      _QF_BV_BINARY_FUNCTION(bvand, tag::bvand_tag)
      _QF_BV_BINARY_FUNCTION(bvnand, tag::bvnand_tag)
      _QF_BV_BINARY_FUNCTION(bvor, tag::bvor_tag)
      _QF_BV_BINARY_FUNCTION(bvnor, tag::bvnor_tag)
      _QF_BV_BINARY_FUNCTION(bvxor, tag::bvxor_tag)
      _QF_BV_BINARY_FUNCTION(bvxnor, tag::bvxnor_tag)

      _QF_BV_BINARY_FUNCTION(bvadd, tag::bvadd_tag)
      _QF_BV_BINARY_FUNCTION(bvmul, tag::bvmul_tag)
      _QF_BV_BINARY_FUNCTION(bvsub, tag::bvsub_tag)
      _QF_BV_BINARY_FUNCTION(bvudiv, tag::bvudiv_tag)
      _QF_BV_BINARY_FUNCTION(bvurem, tag::bvurem_tag)
      _QF_BV_BINARY_FUNCTION(bvsdiv, tag::bvsdiv_tag)
      _QF_BV_BINARY_FUNCTION(bvsrem, tag::bvsrem_tag)

      _QF_BV_BINARY_FUNCTION(bvcomp, tag::bvcomp_tag)

      _QF_BV_BINARY_FUNCTION(bvslt, tag::bvslt_tag)
      _QF_BV_BINARY_FUNCTION(bvsgt, tag::bvsgt_tag)
      _QF_BV_BINARY_FUNCTION(bvsle, tag::bvsle_tag)
      _QF_BV_BINARY_FUNCTION(bvsge, tag::bvsge_tag)

      _QF_BV_BINARY_FUNCTION(bvult, tag::bvult_tag)
      _QF_BV_BINARY_FUNCTION(bvugt, tag::bvugt_tag)
      _QF_BV_BINARY_FUNCTION(bvule, tag::bvule_tag)
      _QF_BV_BINARY_FUNCTION(bvuge, tag::bvuge_tag)

      _QF_BV_BINARY_FUNCTION(bvshl,  tag::bvshl_tag)
      _QF_BV_BINARY_FUNCTION(bvshr,  tag::bvshr_tag)
      _QF_BV_BINARY_FUNCTION(bvashr, tag::bvashr_tag)


      _QF_BV_BINARY_FUNCTION(concat, tag::concat_tag)

#undef _QF_BV_BINARY_FUNCTION

 #define _QF_BV_UNARY_FUNCTION(NAME_, TAG_) \
      template<typename E1> \
      typename proto::result_of::make_expr< TAG_, QF_BV_Domain, E1 const &>::type \
      NAME_( E1 const& e1) \
      { \
        return proto::make_expr< TAG_, QF_BV_Domain >(boost::cref(e1));\
      } 

      // bitwise binary
      _QF_BV_UNARY_FUNCTION(bvnot, tag::bvnot_tag)
      _QF_BV_UNARY_FUNCTION(bvneg, tag::bvneg_tag)

#undef _QF_BV_UNARY_FUNCTION

      // extract operator
      template< typename Expr>
      inline typename proto::result_of::make_expr< tag::extract_tag, QF_BV_Domain
        , unsigned long const & // from
        , unsigned long const & // length
        , Expr const &          // Expr
      > ::type
      extract( unsigned long const & from, unsigned long const & width, Expr const &   e)
      {
        return proto::make_expr< tag::extract_tag, QF_BV_Domain>(boost::cref(from), boost::cref(width), boost::cref(e));
      } 

      // zero_extend operator
      template< typename Expr>
      inline typename proto::result_of::make_expr< tag::zero_extend_tag, QF_BV_Domain
        , unsigned long const & // length
        , Expr const &          // Expr
      > ::type
      zero_extend ( unsigned long const & howMany, Expr const &   e)
      {
        return proto::make_expr< tag::zero_extend_tag, QF_BV_Domain>( boost::cref(howMany), boost::cref(e));
      } 

      // sign_extend operator
      template< typename Expr>
      inline typename proto::result_of::make_expr< tag::sign_extend_tag, QF_BV_Domain
        , unsigned long const & // length
        , Expr const &          // Expr
      > ::type
      sign_extend ( unsigned long const & howMany, Expr const &   e)
      {
        return proto::make_expr< tag::sign_extend_tag, QF_BV_Domain>( boost::cref(howMany), boost::cref(e));
      } 

      // constant creation
      typedef proto::result_of::make_expr< tag::bvuint_tag, QF_BV_Domain
        , unsigned long
        , unsigned long
      > ::type bvuint_result_type;

      inline bvuint_result_type
      bvuint( unsigned long const & value, unsigned long const & width )
      {
        return proto::make_expr< tag::bvuint_tag, QF_BV_Domain>(value, width);
      } 
      
      typedef proto::result_of::make_expr< tag::bvsint_tag, QF_BV_Domain
        , long
        , unsigned long
      > ::type bvsint_result_type;

      inline bvsint_result_type
      bvsint( long const & value, long unsigned const & width )
      {
        return proto::make_expr< tag::bvsint_tag, QF_BV_Domain >( value, width);
      } 

      // bvint: bvuint/bvsint depending on the type of the variable...
      template< typename Integer > 
      typename boost::enable_if< typename boost::mpl::and_<
            boost::is_integral<Integer>,
            boost::is_signed<Integer>
          >::type,
          bvsint_result_type >::type
      bvint( Integer value, unsigned long const & width )
      {
        return proto::make_expr< tag::bvsint_tag, QF_BV_Domain >( (long) value, width);
      }
          
      template< typename Integer > 
      typename boost::enable_if< typename boost::mpl::and_<
            boost::is_integral<Integer>,
            boost::mpl::not_<boost::is_signed<Integer> >
          >::type,
          bvuint_result_type >::type
      bvint( Integer value, unsigned long const & width )
      {
        return proto::make_expr< tag::bvuint_tag, QF_BV_Domain >( (unsigned long) value, width);
      }

       

      inline proto::result_of::make_expr< tag::bvbin_tag, QF_BV_Domain
        , std::string const &
      > ::type
      bvbin( std::string const & value )
      {
        return proto::make_expr< tag::bvbin_tag, QF_BV_Domain >(boost::cref(value));
      } 

      inline proto::result_of::make_expr< tag::bvhex_tag, QF_BV_Domain
        , std::string const &
      > ::type
      bvhex( std::string const & value )
      {
        return proto::make_expr< tag::bvhex_tag, QF_BV_Domain >(boost::cref(value));
      } 


      typedef 
      proto::result_of::make_expr< proto::tag::terminal, QF_BV_Domain
        , tag::var_tag
      > ::type bitvector;

      inline bitvector
      new_bitvector( unsigned width=1 )
      {
        tag::var_tag tag;
        tag.id = impl::new_var_id();
        tag.width= width;
        return proto::make_expr< proto::tag::terminal, QF_BV_Domain >( tag );
      } 

      inline std::size_t hash_value( bitvector const &bv ) {
        tag::var_tag const tag = boost::proto::value(bv);
        std::size_t seed = 0;
        boost::hash_combine(seed, tag.id);
        return seed;
      }

      inline bool operator==(QF_BV< proto::terminal< tag::bit0_tag >::type> const &,
		      QF_BV< proto::terminal< tag::bit0_tag >::type> const &) {
	return true;
      }

      inline bool operator==(QF_BV< proto::terminal< tag::bit1_tag >::type> const &,
		      QF_BV< proto::terminal< tag::bit1_tag >::type> const &) {
	return true;
      }

      inline bool operator==( bitvector const &lhs, bitvector const &rhs ) {
	tag::var_tag const lhs_tag = proto::value(lhs);
	tag::var_tag const rhs_tag = proto::value(rhs);
	return boost::tie(lhs_tag.id, lhs_tag.width) == boost::tie(rhs_tag.id, rhs_tag.width);
      }

      /** @} */

    } // namespace QF_BV
  } // namepace logic
} // namespace metaSMT

//  vim: ft=cpp:ts=2:sw=2:expandtab
