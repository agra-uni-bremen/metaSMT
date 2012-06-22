#pragma once
#include "Features.hpp"
#include "support/protofy.hpp"
#include <boost/proto/debug.hpp>
#include <cstdio>

namespace metaSMT {

  template<typename Solver>
  struct Debug_Context : Solver {};
  
  template <typename Solver, typename Expr>
  void assertion( Debug_Context<Solver> & ctx, Expr const & e )
  {
    std::printf("DEBUG assertion:\n");
    boost::proto::display_expr(detail::protofy(e));
    metaSMT::assertion( (Solver&) ctx, e );
  }
  
  template <typename Solver, typename Expr>
  void assumption( Debug_Context<Solver> & ctx, Expr const & e )
  {
    std::printf("DEBUG assumption:\n");
    boost::proto::display_expr(detail::protofy(e));
    metaSMT::assumption( (Solver&) ctx, e );
  }

  namespace features {
    template<typename Context, typename Feature>
    struct supports< Debug_Context<Context>, Feature>
    : supports<Context, Feature>::type {};
  }

  
} /* metaSMT */

