#pragma once

#include <boost/type_traits/is_same.hpp>

namespace metaSMT {
  namespace type {

    struct Boolean {
      template<typename STREAM> 
      friend STREAM & operator<< (STREAM & out, Boolean const & self) \
      {  return (out << "Boolean"); }

    };

      /** equality of Boolean Types **/
      template <typename T>
      bool operator== (Boolean const & a , T const & b) \
      {  return boost::is_same<T, Boolean>::value; }

  } /* type */
} /* metaSMT */
