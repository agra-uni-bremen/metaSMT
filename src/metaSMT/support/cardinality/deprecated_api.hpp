#pragma once

#include "Evaluator.hpp"

namespace metaSMT {

namespace cardtags = metaSMT::logic::cardinality::tag;

  template<typename Context, typename Boolean>
  typename Context::result_type
  one_hot(Context &ctx, std::vector<Boolean> const &ps) {
    assert(ps.size() > 0 && "One hot encoding requires at least one input variable");

    if (ps.size() == 1) {
      return evaluate(ctx, logic::equal(ps[0], logic::True));
    }

    typename Context::result_type zero_rail = evaluate(ctx, ps[0]);
    typename Context::result_type one_rail = evaluate(ctx, Not(ps[0]));

    for (unsigned u = 1; u < ps.size() - 1; ++u) {
      zero_rail = evaluate(ctx, Ite(ps[u], one_rail, zero_rail));
      one_rail = evaluate(ctx, Ite(ps[u], logic::False, one_rail));
    }

    return evaluate(ctx, Ite(ps[ps.size()-1], one_rail, zero_rail));
  }

  template <typename Context, typename Boolean>
  typename Context::result_type
  cardinality_eq(Context &ctx, std::vector<Boolean> const &ps, unsigned cardinality) {
    return evaluate(ctx,
      cardinality::cardinality(cardtags::eq_tag(), ps, cardinality)
    );
  }

  template <typename Context, typename Boolean>
  typename Context::result_type
  cardinality_geq(Context &ctx, std::vector<Boolean> const &ps, unsigned cardinality) {
    return evaluate(ctx,
      cardinality::cardinality(cardtags::ge_tag(), ps, cardinality)
    );
  }

  template <typename Context, typename Boolean>
  typename Context::result_type
  cardinality_leq(Context &ctx, std::vector<Boolean> const &ps, unsigned cardinality) {
    return evaluate(ctx,
      cardinality::cardinality(cardtags::le_tag(), ps, cardinality)
    );
  }

  template <typename Context, typename Boolean>
  typename Context::result_type
  cardinality_gt(Context &ctx, std::vector<Boolean> const &ps, unsigned cardinality) {
    return evaluate(ctx,
      cardinality::cardinality(cardtags::gt_tag(), ps, cardinality)
    );
  }

  template <typename Context, typename Boolean>
  typename Context::result_type
  cardinality_lt(Context &ctx, std::vector<Boolean> const &ps, unsigned cardinality) {
    return evaluate(ctx,
      cardinality::cardinality(cardtags::lt_tag(), ps, cardinality)
    );
  }
} // metaSMT
