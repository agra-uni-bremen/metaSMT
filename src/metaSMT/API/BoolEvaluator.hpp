#pragma once
#include "Evaluator.hpp"

namespace metaSMT {
  template <>
  struct Evaluator<bool> : public boost::mpl::true_ {
    template < typename Context >
    static typename Context::result_type eval(Context &ctx, bool b) {
      if ( b ) {
        return evaluate(ctx, metaSMT::logic::True);
      }
      else {
        return evaluate(ctx, metaSMT::logic::False);
      }
    }
  }; // Evaluator
} // metaSMT
