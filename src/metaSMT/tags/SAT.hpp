#pragma once

#include <boost/variant.hpp>
#include <boost/mpl/vector.hpp>

namespace metaSMT {

  namespace SAT {
    namespace tag {

    // sat literal tag
    // 0 is invalid
    // n is variable n
    // -m is variable n negated
    struct lit_tag { 
      int id; 
      template<typename STREAM>
      friend STREAM & operator<< (STREAM & out, lit_tag const & self)
      {  out << "sat_lit[" << self.id  << "]"; return out; }
      bool operator< (lit_tag const & other) const { return id < other.id; }
      lit_tag operator- () const { lit_tag l = { -id }; return l; }
      int var() const {return id >= 0 ? id: -id; }
    };

    struct c_tag { 
      template<typename STREAM>
      friend STREAM & operator<< (STREAM & out, c_tag const & self)
      {  out << "or"; return out; }
      bool operator< (c_tag const & other) const { return false; }
    };

    struct not_tag { 
      template<typename STREAM>
      friend STREAM & operator<< (STREAM & out, not_tag const & self)
      {  out << "not"; return out; }
      bool operator< (not_tag const & other) const { return false; }
    };

      // tag variant SAT
      typedef boost::mpl::vector<
          lit_tag
        , c_tag
      >::type SAT_Tags;

      typedef boost::make_variant_over< SAT_Tags >::type SAT_Tag;

    } // namespace tag
  } // namespace SAT
} // namespace metaSMT

//  vim: ft=cpp:ts=2:sw=2:expandtab
