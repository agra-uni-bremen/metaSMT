#pragma once
#include "../../API/Evaluator.hpp"

namespace metaSMT {
  template < typename Tag, typename Boolean >
  struct Evaluator< cardinality::Cardinality<Tag, Boolean> > : public boost::mpl::true_ {
    template < typename Context >
    static typename Context::result_type
    eval(Context &ctx, cardinality::Cardinality<Tag, Boolean> const &c) {
      std::string enc = c.encoding;
      if ( enc == "" ) {
        enc = get_option(ctx, "cardinality", /* default = */ "bdd");
      }

      if ( enc == "adder" ) {
        return cardinality::adder::cardinality(ctx, c);
      }
      else if ( enc == "bdd" ) {
        return cardinality::bdd::cardinality(ctx, c);
      }
      else {
        assert( false && "Unknown cardinality implementation" );
        throw std::exception();
      }
    }
  }; // Evaluator
} // metaSMT
