#pragma once

#include "../Features.hpp"

namespace metaSMT {
  // Note that void is not a valid result_type, i.e., simplify will
  // fail when a graph solver is used.
  struct simplify_cmd { typedef void result_type; };

  /**
   * \brief simplify function
   * \param ctx The context to work on
   * \param e expression to be simplified
   * \return simplified expression
   *
   */
  template <typename Context, typename Expr >
  typename boost::enable_if<
    features::supports<Context, simplify_cmd>
  , typename Context::result_type
  >::type
  simplify( Context &ctx, Expr const &e ) {
    return ctx.command(simplify_cmd(), evaluate(ctx, e) );
  }

  /** \cond */
  // return the original expression if simplify is unsupported
  template <typename Context, typename Expr >
  typename boost::disable_if<
    features::supports<Context, simplify_cmd>
  , typename Context::result_type
  >::type
  simplify( Context &ctx, Expr const &e ) {
    return evaluate(ctx, e);
  }

  /**@}*/

} /* metaSMT */
