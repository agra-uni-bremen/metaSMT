#pragma once

namespace metaSMT {
  namespace type {
    struct Array {
      Array() {}

      Array(unsigned elem_width,
            unsigned index_width)
        : elem_width(elem_width)
        , index_width(index_width)
      {}

      template <typename STREAM>
      friend STREAM & operator<<(STREAM & out, Array const &self) \
      { return (out << "Array [" << self.elem_width << "," << self.index_width << "]"); }

      unsigned elem_width;
      unsigned index_width;
    };

    // equality of Array types
    template <typename T>
    typename boost::enable_if< boost::is_same<type::Array, T>, bool>::type
    operator== (type::Array const &a , T const &b)                      \
    { return a.elem_width == b.elem_width && a.index_width == b.index_width; }

    template <typename T>
    typename boost::disable_if< boost::is_same<type::Array, T>, bool>::type
    operator== (type::Array const &a , T const &b)  \
    { return false; }

  } // type
} // metaSMT
