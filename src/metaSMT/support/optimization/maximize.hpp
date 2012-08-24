#pragma once

#include "detail.hpp"
#include "../cardinality.hpp"

namespace metaSMT {
  namespace optimization {
    template < typename Context, typename Boolean >
    unsigned maximize( Context &ctx, std::vector<Boolean> const &ps,
                       unsigned min, unsigned max ) {
      unsigned mid = min, last_mid = min;
      bool sat = false;
      while ( max >= min ) {
        mid = min + ((max - min) >> 1);
        assumption(ctx, cardinality_geq(ctx, ps, mid));
        sat = solve(ctx);
        if ( sat ) {
          unsigned const witness = detail::countOnes(ctx, ps);
          min = witness + 1;
          last_mid = witness;
        }
        else {
          max = mid - 1;
        }
      }
      return last_mid;
    }

    template < typename Context, typename Boolean >
    unsigned maximize( Context &ctx, std::vector<Boolean> const &ps,
                       unsigned max ) {
      unsigned const lower_bound = detail::countOnes(ctx, ps);
      assert( lower_bound >= 0 );
      return maximize(ctx, ps, lower_bound, max);
    }

    template < typename Context, typename Boolean >
    unsigned maximize( Context &ctx, std::vector<Boolean> const &ps ) {
      return maximize(ctx, ps, ps.size());
    }
  } // optimization
} // metaSMT
