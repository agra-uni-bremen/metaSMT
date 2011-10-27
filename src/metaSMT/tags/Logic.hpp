#pragma once

#include <boost/variant.hpp>
#include <boost/mpl/vector.hpp>

namespace metaSMT {
  struct nil { 
    bool operator< (nil const &) const { return false; };
    template<typename STREAM> friend STREAM & 
      operator<< (STREAM & out, nil const & ) {  out << "nil"; return out; }
  };

  namespace logic {
    namespace tag {

#define PRINT(Tag, body) template<typename STREAM> \
  friend STREAM & operator<< (STREAM & out, Tag const & self) \
  {  out << body; return out; }
#define TAG( NAME ) struct  NAME##_tag { \
  bool operator<(NAME##_tag const &) const {return false;} \
  PRINT(NAME##_tag, #NAME) \
};
      
    // variable tag
    struct var_tag { unsigned id; 
      PRINT(var_tag, "var_tag[" << self.id  << "]")
      bool operator< (var_tag const & other) const {
        return id < other.id;
      }
    };

    // constants
    TAG(true)
    TAG(false)
    TAG(bool)

    // unary
    TAG(not)

    // binary
    TAG(equal)
    TAG(nequal)
    TAG(implies)

    TAG(and)
    TAG(nand)
    TAG(or)
    TAG(nor)
    TAG(xor)
    TAG(xnor)

    TAG(ite)

#undef PRINT
#undef TAG
    //
      // tag variant Predicate
      typedef boost::mpl::vector<
          false_tag
        , true_tag
        , bool_tag
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
