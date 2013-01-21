#pragma once

#include "attribute.hpp"
#include <boost/variant.hpp>
#include <boost/mpl/vector.hpp>

namespace metaSMT {
  struct nil { 
    typedef attr::ignore attribute;

    bool operator< (nil const &) const { return false; };
    template<typename STREAM> friend STREAM & 
      operator<< (STREAM & out, nil const & ) {  out << "nil"; return out; }
  };

  namespace logic {
    namespace tag {

#define PRINT(Tag, body) template<typename STREAM> \
  friend STREAM & operator<< (STREAM & out, Tag const & self) \
  {  out << body; return out; }
#define TAG( NAME, ATTR ) struct NAME##_tag { \
  typedef attr::ATTR attribute; \
  bool operator<(NAME##_tag const &) const {return false;} \
  PRINT(NAME##_tag, #NAME) \
};
      
    // variable tag
    struct var_tag { unsigned id; 
      typedef attr::ignore attribute;

      PRINT(var_tag, "var_tag[" << self.id  << "]")
      bool operator< (var_tag const & other) const {
        return id < other.id;
      }
    };

    // constants
    TAG(true, constant)
    TAG(false, constant)
    TAG(bool, constant)

    // unary
    TAG(not, unary)

    // binary
    TAG(equal, binary)
    TAG(nequal, binary)
    TAG(implies, binary)

    TAG(and, binary)
    TAG(nand, binary)
    TAG(or, binary)
    TAG(nor, binary)
    TAG(xor, binary)
    TAG(xnor, binary)

    // ternary
    TAG(ite, ternary)

#undef PRINT
#undef TAG
    //
      // tag variant Predicate
      typedef boost::mpl::vector<
          false_tag
        , true_tag
        , not_tag
        , equal_tag
        , nequal_tag
        , and_tag
        , nand_tag
        , or_tag
        , nor_tag
        , xor_tag
        , xnor_tag
        , implies_tag
        , ite_tag
        , var_tag
      >::type Predicate_Tags;

      typedef boost::make_variant_over< Predicate_Tags >::type Predicate_Tag;

    } // namespace tag
  } // namespace logic
} // namespace metaSMT

//  vim: ft=cpp:ts=2:sw=2:expandtab
