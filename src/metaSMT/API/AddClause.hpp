
#pragma once

#include "../tags/SAT.hpp"
#include "../Features.hpp"

#include <boost/mpl/assert.hpp>

namespace metaSMT
{
  namespace features
  {
    struct addclause_api {};
  }

  struct addclause_cmd { typedef void result_type; };

  template<typename Context_>
  void add_clause ( Context_& ctx, std::vector < SAT::tag::lit_tag > const& clause )
  {
    BOOST_MPL_ASSERT_MSG(
        ( features::supports< Context_, features::addclause_api>::value),
        context_does_not_support_addclause_api,
        ()
    );

    ctx.command ( addclause_cmd(), clause );
  }
}
