#pragma once

#include "../Features.hpp"

namespace metaSMT {
  struct assertion_cmd { typedef void result_type; };
  
  /**
   * \brief Assertion API
   *
   *
   * \code
   *  DirectSolver_Context< Boolector > ctx;
   *
   *  assertion(ctx,  True);
   *  solve(ctx) == true;
   *
   *  assertion(ctx, False)
   *  solve(ctx) == true;
   * \endcode
   * \ingroup API
   * \defgroup Assertion Assertion
   * @{
   */

  /**
   * \brief add an assumption to the current context
   *
   * \param ctx The metaSMT Context
   * \param e Any Boolean expression
   */
  template <typename Context_, typename Expr_>
  void assertion( Context_ & ctx, Expr_ const & e )
  {
    BOOST_MPL_ASSERT_MSG(
        ( features::supports< Context_, assertion_cmd>::value),
        context_does_not_support_assertion_api,
    );

    ctx.command(assertion_cmd(),  evaluate(ctx, e) );
  }
} /* metaSMT */
