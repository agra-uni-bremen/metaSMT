#pragma once

#include <vector>

namespace metaSMT {
  namespace cardinality {
    namespace tag {
      struct eq_tag {};
      struct lt_tag {};
      struct leq_tag {};
      struct geq_tag {};
      struct gt_tag {};
    } // tag

    template < typename Tag, typename Boolean >
    struct Cardinality {
      Cardinality( std::vector< Boolean > const &ps,
                   unsigned const cardinality,
                   std::string const encoding = "" )
        : ps(ps)
        , cardinality(cardinality)
        , encoding(encoding)
      {}

      std::vector< Boolean > const &ps;
      unsigned const cardinality;
      std::string const encoding;
    }; // Cardinality

    template < typename Tag, typename Boolean >
    Cardinality<Tag, Boolean> cardinality(
      Tag const &
    , std::vector< Boolean > const &ps
    , unsigned const cardinality
    , std::string const encoding = "" )
    {
      return Cardinality<Tag, Boolean>( ps, cardinality, encoding);
    }

  } // cardinality
} // metaSMT
