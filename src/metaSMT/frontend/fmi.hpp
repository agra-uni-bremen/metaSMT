#pragma once
/*
 * =====================================================================================
 *
 *       Filename:  fmi.hpp
 *
 *    Description:  Representing the FMI Grammar 
 *
 *        Version:  1.0
 *        Created:  02/08/2010 09:55:11 AM
 *       Revision:  none
 *       Compiler:  gcc
 *
 *         Author:  Stefan Frehse (sfrehse), sfrehse@informatik.uni-bremen.de
 *        Company:  University of Bremen, Germany
 *
 * =====================================================================================
 */

#include "../transform/fmiToQF_BV.hpp"

// Boost includes
//
#include <boost/proto/core.hpp> 
#include <boost/proto/debug.hpp> 
#include <boost/mpl/int.hpp> 
#include <boost/dynamic_bitset.hpp>

#include <vector>

namespace metaSMT {

/** 
 * @brief fmi, the formal methods interface is an wrapper to make the transition
 * from revkit/fmi easy. (Experimental)
 *
 * It tries to overlaod operators in the same way as revkit/fmi does.
 *
 * @warning Experimental frontend, will most likely not work
 *
 * @ingroup frontend
 **/
  namespace fmi
  {
    namespace proto = boost::proto;
    namespace mpl = boost::mpl;

    struct grammar; 

    struct grammar_cases
    {
      template<typename Tag>
        struct case_ : proto::not_<proto::_> {};
    };

    template<typename I>
    struct placeholder
    {
      typedef I arity;
    }; 

    template<typename Stream, typename I>
    Stream & operator<< (Stream & o, placeholder<I>) {
      o << "placeholder<" <<I::value << ">"; return o;
    }

    // Terminal definition
    template<>
      struct grammar_cases::case_<proto::tag::terminal> :
      proto::or_<
      proto::terminal < placeholder <mpl::int_<0> > >,
      proto::terminal < placeholder <mpl::int_<1> > >,
      proto::terminal < placeholder <mpl::int_<2> > >,
      proto::terminal < placeholder <mpl::int_<3> > >,
      proto::terminal < placeholder <mpl::int_<4> > >,
      proto::terminal < placeholder <mpl::int_<5> > >,
      proto::terminal < placeholder <mpl::int_<6> > >
        //, proto::terminal< integral_wrapper < unsigned int > >
        >
        {};


    // bitwise operator 
    template<>
      struct grammar_cases::case_<proto::tag::bitwise_and> :  proto::bitwise_and < grammar, grammar > {};
    template<>
      struct grammar_cases::case_<proto::tag::bitwise_xor> :  proto::bitwise_xor < grammar, grammar > {};

    //  template<>
    //    struct grammar_cases::case_<proto::tag::function> : 
    //    proto::function
    //      < zero_extend_tag,  
    //          proto::terminal<integral_wrapper < unsigned int> > ,
    //          grammar > {};


    template<>
      struct grammar_cases::case_<proto::tag::subscript> : proto::subscript < grammar, grammar > {};


    template<>
      struct grammar_cases::case_<proto::tag::modulus_assign> : proto::modulus_assign < grammar, grammar > {};

    template<>
      struct grammar_cases::case_<proto::tag::not_equal_to> : proto::not_equal_to < grammar, grammar > {};

    template<>
    struct grammar_cases::case_<proto::tag::equal_to> : proto::equal_to < grammar, grammar > {};

  template<>
    struct grammar_cases::case_<proto::tag::shift_left> : proto::shift_left < grammar, grammar > {};


    //  template<>
    //    struct grammar_cases::case_<proto::tag::function> : proto::function<ite_tag, grammar, grammar, grammar > {};


    //  template<>
    //    struct grammar_cases::case_<proto::tag::if_else_> : proto::if_else_ < grammar, grammar, grammar > {};


    struct grammar :
      //proto::switch_<grammar_cases> {};
      proto::not_< proto::address_of< proto::_> >
    {};



    struct Solver {};
    template<typename Stream>
    Stream & operator<< (Stream & o, Solver) {
      o << "generate"; return o;
    }


  template<typename T>
  struct constraint;

  struct constraint_domain 
    : proto::domain < proto::generator < constraint >, grammar > 
  { };

  template<typename T>
  struct constraint  : proto::extends <T, constraint<T>, constraint_domain>
  { 
    typedef proto::extends<T, constraint<T>, constraint_domain> base_type;

    constraint (T expr = T())
    : base_type (expr) { } 
  };

  // define variables
    typedef 
    proto::result_of::make_expr< proto::tag::terminal, constraint_domain
      , logic::QF_BV::tag::var_tag
    > ::type bv;

    template<typename Context>
    bv new_variable(Context &, unsigned width) {
      logic::QF_BV::tag::var_tag tag;
      tag.id = impl::new_var_id();
      tag.width= width;
      return proto::make_expr< proto::tag::terminal, constraint_domain >( tag );
    }

    template<typename T1, typename T2> 
    bv zero_extend (T1, T2, unsigned) {return bv();}

  // define some placeholders
  typedef constraint<proto::terminal<placeholder<mpl::int_<0> > >::type> var0_type;
  typedef constraint<proto::terminal<placeholder<mpl::int_<1> > >::type> var1_type;
  typedef constraint<proto::terminal<placeholder<mpl::int_<2> > >::type> var2_type;
  typedef constraint<proto::terminal<placeholder<mpl::int_<3> > >::type> var3_type;
  typedef constraint<proto::terminal<placeholder<mpl::int_<4> > >::type> var4_type;
  typedef constraint<proto::terminal<placeholder<mpl::int_<5> > >::type> var5_type;
 
  //typedef constraint<proto::terminal<zero_extend_tag>::type> zero_extend;

  //typedef constraint<proto::terminal<ite_tag>::type > ite_;

  // define default named placeholder 
  var0_type const _0;
  var1_type const _1;
  var2_type const _2;
  var3_type const _3;
  var4_type const _4;
  var5_type const _5;

  template<typename SolverVariant>
  std::vector<boost::dynamic_bitset<> > get_assignment_vector (
      const Solver & solver, 
      const std::vector<bv>& vars)
  {
    return std::vector< boost::dynamic_bitset<> > ();
  }

  struct Generate {
    typedef void result_type;

    template < typename Context, typename Expression >
    void operator() ( Context & ctx, Expression e ) {
      proto::display_expr( transform::fmiToQF_BV()(e) );
      //assertion(ctx, transform::fmiToQF_BV()(e));
    }
    // overload with params
    template < typename Context, typename Expression >
    void operator() ( Context & ctx, Expression e, bv arg0 )
    {  (*this)(ctx, e);  }
    template < typename Context, typename Expression >
    void operator() ( Context & ctx, Expression e, bv arg0, bv arg1 )
    {  (*this)(ctx, e);  }
    template < typename Context, typename Expression >
    void operator() ( Context & ctx, Expression e, bv arg0, bv arg1, bv arg2 )
    {  (*this)(ctx, e);  }
    template < typename Context, typename Expression >
    void operator() ( Context & ctx, Expression e, bv arg0, bv arg1, bv arg2, bv arg3 )
    { (*this)(ctx, e); }
  } generate;

    template < typename Context, typename Expression >
    void assertion ( Context & ctx, Expression e ) { 
      transform::fmiToQF_BV to_QF_BV;
      proto::display_expr( to_QF_BV (e) );
      metaSMT::assertion( ctx, to_QF_BV(e) );
    }

  } /* fmi */
} /* metaSMT */


// vim: tabstop=2 shiftwidth=2 expandtab
