#pragma once

namespace metaSMT {
  namespace optimization {
    namespace detail {
      /*
       * Note that countOnes implicitly calls solve(.).
       */
      template < typename Context, typename Boolean >
      unsigned countOnes( Context &ctx, std::vector<Boolean> const &ps ) {
        bool sat = solve(ctx);
        assert( sat && "The formula must not be unsatisfiable" );
        unsigned num_ones = 0;
        for ( unsigned u = 0; u < ps.size(); ++u ) {
          num_ones += static_cast<bool>(read_value(ctx, ps[u]));
        }
        return num_ones;
      }
    } // detail
  } // optimization
} // metaSMT
