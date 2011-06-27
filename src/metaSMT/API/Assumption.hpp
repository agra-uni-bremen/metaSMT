#pragma once

#include "../Features.hpp"

namespace metaSMT {
  struct assumption_cmd { typedef void result_type; };
  
  /**
   * \brief Assumption API, one-time Assertions
   *
   *
   * \code
   *  DirectSolver_Context< Boolector > ctx;
   *
   *  assumption(ctx,  False);
   *  solve(ctx) == false;
   *  // solve was called, assumption no longer valid
   *
   *  solve(ctx) == true;
   * \endcode
   * \ingroup API
   * \defgroup Assumption Assumption
   * @{
   */

  /**
   * \brief add an assumption to the current context
   *
   * \param ctx The metaSMT Context
   * \param e Any Boolean expression
   */
  template <typename Context_, typename Expr_>
  void assumption( Context_ & ctx, Expr_ const & e )
  {
    BOOST_MPL_ASSERT_MSG(
        ( features::supports< Context_, assumption_cmd>::value),
        context_does_not_support_assumption_api,
    );

    ctx.command(assumption_cmd(),  evaluate(ctx, e) );
  }
} /* metaSMT */
