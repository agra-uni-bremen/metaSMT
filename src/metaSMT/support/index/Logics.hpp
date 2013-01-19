#pragma once
#include "../../tags/Logics.hpp"
#include <boost/mpl/find.hpp>

namespace metaSMT {
  namespace logic {
    typedef int index;

    template < typename Tag >
    struct Index {
      typedef typename boost::mpl::find<
        _all_logic_tags::all_Tags
      , Tag
      >::type iterator;

      static const index value = iterator::pos::value;
    }; // Index
  } // logic
} // metaSMT
