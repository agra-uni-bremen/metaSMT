#pragma once

#include "../Features.hpp"

namespace metaSMT {
  struct assertion_cmd { typedef void result_type; };
  
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
