#pragma once

#include "detail.hpp"
#include "../cardinality.hpp"

namespace metaSMT {
  namespace optimization {
    template < typename Context, typename Boolean >
    unsigned minimize( Context &ctx, std::vector<Boolean> const &ps,
                       unsigned min, unsigned max ) {
      unsigned mid = max, last_mid = max;
      bool sat = false;
      while ( min <= max ) {
        mid = min + ((max - min) >> 1);
        assumption(ctx, cardinality_leq(ctx, ps, mid));
        sat = solve(ctx);
        if ( sat ) {
          unsigned const witness = detail::countOnes(ctx, ps);
          if ( witness <= min ) return min;
          max = witness - 1;
          last_mid = witness;
        }
        else {
          min = mid + 1;
        }
      }
      return last_mid;
    }

    template < typename Context, typename Boolean >
    unsigned minimize( Context &ctx, std::vector<Boolean> const &ps,
                       unsigned min = 0 ) {
      unsigned const upper_bound = detail::countOnes(ctx, ps);
      assert( upper_bound <= ps.size() );
      return minimize(ctx, ps, min, upper_bound);
    }
  } // optimization
} // metaSMT
