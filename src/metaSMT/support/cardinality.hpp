#pragma once

#include <metaSMT/frontend/Logic.hpp>

using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::logic;

namespace metaSMT {

  template<typename Context, typename Boolean>
  typename Context::result_type
  one_hot(Context &ctx, std::vector<Boolean> const &ps) {
    assert(ps.size() > 0 && "One hot encoding requires at least one input variable");

    if (ps.size() == 1) {
      return evaluate(ctx, equal(ps[0], True));
    }

    typename Context::result_type zero_rail = evaluate(ctx, ps[0]);
    typename Context::result_type one_rail = evaluate(ctx, Not(ps[0]));

    for (unsigned u = 1; u < ps.size() - 1; ++u) {
      zero_rail = evaluate(ctx, Ite(ps[u], one_rail, zero_rail));
      one_rail = evaluate(ctx, Ite(ps[u], False, one_rail));
    }

    return evaluate(ctx, Ite(ps[ps.size()-1], one_rail, zero_rail));
  }

  template <typename Context, typename Boolean>
  typename Context::result_type
  cardinality_geq(Context &ctx, std::vector<Boolean> const &ps, unsigned cardinality) {
    assert(ps.size() > 0 && "Greater equal cardinality constraint requires at least one input variable");
    
    if (ps.size() < cardinality) {
      return evaluate(ctx, False);
    }

    if (ps.size() == cardinality) {
      typename Context::result_type res = evaluate(ctx, True);
      for (unsigned u = 0; u < ps.size(); ++u)
        res = evaluate(ctx, And(res, ps[u]));
      return res;
    }

    if (cardinality == 0) {
      return evaluate(ctx, True);
    }

    // Now: 0 <= cardinality < ps.size()
    unsigned const rail_size = cardinality;
    std::vector<typename Context::result_type> rails[2];
    rails[0].resize(rail_size);
    rails[1].resize(rail_size);
    
    // Tableau algorithm - Iteratively calculate all elements
    for (unsigned v = 0; v < ps.size() - cardinality + 1; ++v) {
      for (unsigned u = 0; u < cardinality; ++u) {
        if (u == 0 && v == 0) {
          rails[0][0] = evaluate(ctx, ps[0]);
        } else if (u == 0) {
          rails[v%2][0] = evaluate(ctx, Ite(evaluate(ctx, ps[v]), True, rails[(v-1)%2][0]));
        } else if (v == 0) {
          rails[0][u] = evaluate(ctx, Ite(evaluate(ctx, ps[u]), rails[0][u-1], False)); 
        } else {
          rails[v%2][u] = evaluate(ctx, Ite(ps[u+v], rails[v%2][u-1], rails[(v-1)%2][u]));
        }
      }
    }
    return rails[(ps.size() - cardinality) % 2][cardinality - 1];
  }

  template <typename Context, typename Boolean>
  typename Context::result_type
  cardinality_lt(Context &ctx, std::vector<Boolean> const &ps, unsigned cardinality) {
    assert(ps.size() > 0 && "Lower than cardinality constraint requires at least one input variable");
    return evaluate(ctx, Not(cardinality_geq(ctx, ps, cardinality)));
  }
 
  template <typename Context, typename Boolean>
  typename Context::result_type
  cardinality_eq(Context &ctx, std::vector<Boolean> const &ps, unsigned cardinality) {
    assert(ps.size() > 0 && "Equality cardinality constraint requires at least one input variable");
    return evaluate(ctx, And(cardinality_geq(ctx, ps, cardinality), cardinality_lt(ctx, ps, cardinality+1)));
  }

} // metaSMT

