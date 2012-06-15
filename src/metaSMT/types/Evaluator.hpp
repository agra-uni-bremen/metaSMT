#pragma once
#include "../API/Evaluator.hpp"

namespace metaSMT {
  template < typename Ctx >
  struct Evaluator< type::TypedSymbol<Ctx> > : public boost::mpl::true_ {
    template < typename Context >
    static typename Context::result_type eval(Context &ctx, metaSMT::type::TypedSymbol<Ctx> s) {
      return s.eval(ctx);
    }
  }; // Evaluator
} // metaSMT
