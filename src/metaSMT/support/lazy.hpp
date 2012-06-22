#pragma once

#include "protofy.hpp"

#include <boost/proto/core.hpp>
#include <boost/proto/debug.hpp>
#include <boost/proto/transform.hpp>
#include <boost/proto/functional/fusion/at.hpp>
#include <boost/fusion/container/generation/make_vector.hpp>

namespace metaSMT {

  namespace detail {
    // implementation details
    
    template <typename N>
    struct argument
    { 
      typedef N type;
      enum { value = N::value };
    };

    //template<typename O, typename N>
    //O& operator<< (O & out, argument<N> const & ) {
    //  return out << "arg" << (N::value+1);
    //}

    struct replace_args 
    : proto::or_<
        proto::when<proto::terminal< argument<proto::_> >
          , boost::proto::functional::at( proto::_state, proto::_value )
        >
      , proto::nary_expr<proto::_, proto::vararg<replace_args> >
    > {};


    template <typename Context, typename Expr>
    struct lazy_call {

      lazy_call(Context& ctx, Expr const & e)
      : ctx_( ctx )
      , e_( proto::deep_copy(e) )
      { }

      template<typename Arg1> 
      typename Context::result_type operator() ( Arg1 const & arg1)
      {
        return evaluate(ctx_, replace_args()(e_, 
          boost::fusion::make_vector( protofy(arg1) )
        ));
      }

      template<typename Arg1, typename Arg2> 
      typename Context::result_type operator() ( Arg1 const & arg1
        , Arg2 const & arg2 )
      {
        return evaluate(ctx_, replace_args()(e_, 
          boost::fusion::make_vector( protofy(arg1), protofy(arg2) )
        ));
      }

      template<typename Arg1, typename Arg2, typename Arg3> 
      typename Context::result_type operator() ( Arg1 const & arg1
        , Arg2 const & arg2, Arg3 const & arg3 )
      {
        return evaluate(ctx_, replace_args()(e_, 
          boost::fusion::make_vector(protofy(arg1), protofy(arg2), protofy(arg3))
        ));
      }

      typename proto::result_of::deep_copy<Expr>::type e_;
      Context & ctx_;
    };
    
  } /* detail */

  /** 
   * @brief lazy evaluation of expressions with arguments
   *
   * lazy created a polymorphic function object that, when called
   * evaluates the enclosed expression.
   *
   * lazy can be used store an expression in a function
   * @code
   * boost::function< result_type ( predicate const &, predicate const & ) > 
   *   andiN = metaSMT::lazy( ctx, And( arg1, Not(arg2)) ) ;
   * @endcode
   *
   * or to use in stl algorithms:
   * @code
   * std::vector< result_type > expr;
   * ...
   * tmp = std::accumulate(expr.begin(), expr.end(), initial,
   *    metaSMT::lazy(ctx, Xor(arg1, arg2) )
   * );
   * @endcode
   *
   * @ingroup Support
   * @defgroup Lazy Lazy expression evaluation
   * @{
   */

  /**
   * @brief create a functor from an expression
   */
  template< typename Context, typename Expr>
  detail::lazy_call< Context, Expr > 
  lazy(Context & ctx, Expr const & e)
  {
    return detail::lazy_call< Context, Expr> (ctx, e);
  }

  /**
   * @brief placeholder for an argument of lazy 
   */
  static const detail::argument< boost::mpl::int_<0> > arg1 = {};
  /**
   * @brief placeholder for an argument of lazy 
   */
  static const detail::argument< boost::mpl::int_<1> > arg2 = {};
  /**
   * @brief placeholder for an argument of lazy 
   */
  static const detail::argument< boost::mpl::int_<2> > arg3 = {};

  /**@}*/
} /* metaSMT */


