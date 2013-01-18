#pragma once
#include <boost/mpl/string.hpp>
#include <boost/mpl/insert_range.hpp>
#include <boost/mpl/end.hpp>

namespace metaSMT {
  template < typename str1, typename str2 >
  struct string_concat
    : boost::mpl::insert_range<
        str1
      , typename boost::mpl::end<str1>::type, str2
      >
  {}; // string_concat
} // metaSMT
