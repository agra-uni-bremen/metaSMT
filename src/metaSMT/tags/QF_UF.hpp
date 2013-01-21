#pragma once
#ifndef HEADER_metaSMT_TAG_QF_UF_HPP
#define HEADER_metaSMT_TAG_QF_UF_HPP

#include "Logic.hpp"
#include "../types/Types.hpp"

#include <boost/mpl/vector.hpp>
#include <boost/variant.hpp>

namespace metaSMT {
  namespace logic {
    namespace QF_UF {
      namespace tag {

#define PRINT(Tag, body) template<typename STREAM> \
  friend STREAM & operator<< (STREAM & out, Tag const & self) \
  { return (out << body); }

        // uninterpreted function variable tag
        struct function_var_tag {
          typedef attr::ignore attribute;

          unsigned id;
          type::any_type result_type;
          std::vector<type::any_type> args;

          PRINT(function_var_tag, "function_var_tag[" << self.id << "]")
          bool operator< (function_var_tag const & other) const {
            return id < other.id;
          }
        };

#undef PRINT

        typedef boost::mpl::vector<
          nil
        , function_var_tag
        >::type QF_UF_Tags;

        typedef boost::make_variant_over<QF_UF_Tags>::type QF_UF_Tag;

      } // namespace metaSMT::logic::QF_UF::tag
    } // namespace metaSMT::logic::QF_UF
  } // namespace metaSMT::logic
} // namespace metaSMT
#endif // HEADER_metaSMT_TAG_ARRAY_HPP
//  vim: ft=cpp:ts=2:sw=2:expandtab
