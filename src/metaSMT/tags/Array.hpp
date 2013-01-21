#pragma once
#ifndef HEADER_metaSMT_TAG_ARRAY_HPP
#define HEADER_metaSMT_TAG_ARRAY_HPP

#include "Logic.hpp"

#include <boost/mpl/vector.hpp>
#include <boost/variant.hpp>

namespace metaSMT {
  namespace logic {
    namespace Array {
      namespace tag {

#define PRINT(Tag, body) template<typename STREAM> \
  friend STREAM & operator<< (STREAM & out, Tag const & self) \
  { return (out << body); }
#define TAG( NAME, ATTR ) struct NAME##_tag { \
  typedef attr::ATTR attribute; \
  bool operator<(NAME##_tag const &) const {return false;} \
  PRINT(NAME##_tag, #NAME) \
};

        // array variable tag
        struct array_var_tag {
          typedef attr::ignore attribute;

          unsigned id;
          unsigned elem_width;
          unsigned index_width;
          PRINT(array_var_tag, "array_var_tag[" << self.id  << ',' << self.elem_width << ',' << self.index_width << "]")
          bool operator< (array_var_tag const & other) const {
            return id < other.id;
          }
        };

        TAG(select, ignore)
        TAG(store, ignore)

#undef PRINT
#undef TAG

        typedef boost::mpl::vector<
          nil
        , select_tag
        , store_tag
        , array_var_tag
        >::type Array_Tags;

        typedef boost::make_variant_over<Array_Tags>::type Array_Tag;

      } // namespace metaSMT::logic::Array::tag
    } // namespace metaSMT::logic::Array
  } // namespace metaSMT::logic
} // namespace metaSMT
#endif // HEADER_metaSMT_TAG_ARRAY_HPP
//  vim: ft=cpp:ts=2:sw=2:expandtab
