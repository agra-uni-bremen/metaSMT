#pragma once

#include "../Features.hpp"

namespace metaSMT {
  struct assumption_cmd { typedef void result_type; };
  
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
