#pragma once

#include <boost/type_traits/is_same.hpp>
#include <boost/utility/enable_if.hpp>

namespace metaSMT {
  namespace type {

    struct BitVector {

      unsigned width;

      BitVector() {}

      BitVector(unsigned w)
        : width(w)
      {}

      template<typename STREAM> 
      friend STREAM & operator<< (STREAM & out, BitVector const & self) \
      {  return (out << "BitVector [" << self.width <<"]"); }

    };

    /** equality of BitVector Types **/
    template <typename T>
    typename boost::enable_if< boost::is_same<BitVector, T>, bool>::type
    operator== (BitVector const & a , T const & b)  \
    {  return a.width==b.width; }

    template <typename T>
    typename boost::disable_if< boost::is_same<BitVector, T>, bool>::type
    operator== (BitVector const & a , T const & b)  \
    {  return false; }

  } /* type */
} /* metaSMT */
