#pragma once
#ifndef HEADER_metaSMT_TAG_QF_BV_HPP
#define HEADER_metaSMT_TAG_QF_BV_HPP

#include "Logic.hpp"

#include <boost/mpl/vector/vector40.hpp>
#include <boost/variant.hpp>

namespace metaSMT {
  namespace logic {
    namespace QF_BV {
      /**
       * @brief tags for SMT metaSMT::logic::QF_BV
       **/
      namespace tag {

#define PRINT(Tag, body) template<typename STREAM> \
  friend STREAM & operator<< (STREAM & out, Tag const & self) \
  { return (out << body); }
#define TAG( NAME ) struct  NAME##_tag { \
  bool operator<(NAME##_tag const &) const {return false;} \
  PRINT(NAME##_tag, #NAME) \
};

        

        // variable tag
        struct var_tag { unsigned id; unsigned width; 
          PRINT(var_tag, "bv_var_tag[" << self.id << ',' << self.width << "]")
          bool operator< (var_tag const & other) const {
            return id < other.id;
          }
        };

        // operation tags
        TAG(bit0)
        TAG(bit1)

        // unary
        TAG(bvnot)
        TAG(bvneg)

        // bitwise binary
        TAG(bvand)
        TAG(bvnand)
        TAG(bvor)
        TAG(bvnor)
        TAG(bvxor)
        TAG(bvxnor)


        TAG(bvcomp)

        // bitvec arithmetic
        TAG(bvadd)
        TAG(bvmul)
        TAG(bvsub)
        TAG(bvsdiv)
        TAG(bvsrem)
        TAG(bvudiv)
        TAG(bvurem)

        // bitvector constant creation
        TAG(bvuint)
        TAG(bvsint)
        TAG(bvbin)
        TAG(bvhex)


        // modifying bv length
        TAG(concat)
        TAG(extract)
        TAG(repeat)
        TAG(zero_extend)
        TAG(sign_extend)

        // bitvector shifting
        TAG(bvshl)
        TAG(bvshr)
        TAG(bvashr)

        // comparison operators
        TAG(bvslt)
        TAG(bvsgt)
        TAG(bvsle)
        TAG(bvsge)
        TAG(bvult)
        TAG(bvugt)
        TAG(bvule)
        TAG(bvuge)

#undef PRINT
#undef TAG

      // tag variant QF_BV_Tag
      typedef boost::mpl::vector39<
          nil
        , bit0_tag
        , bit1_tag
        , bvnot_tag
        , bvneg_tag
        , bvand_tag
        , bvnand_tag
        , bvor_tag
        , bvnor_tag
        , bvxor_tag
        , bvxnor_tag
        , bvcomp_tag
        , bvadd_tag
        , bvmul_tag
        , bvsub_tag
        , bvsrem_tag
        , bvsdiv_tag
        , bvurem_tag
        , bvudiv_tag
        , bvuint_tag
        , bvsint_tag
        , bvbin_tag
        , bvhex_tag
        , bvslt_tag
        , bvsgt_tag
        , bvsle_tag
        , bvsge_tag
        , bvult_tag
        , bvugt_tag
        , bvule_tag
        , bvuge_tag
        , concat_tag
        , extract_tag
        , zero_extend_tag
        , sign_extend_tag
        , bvshl_tag
        , bvshr_tag
        , bvashr_tag
        , var_tag
      >::type QF_BV_Tags;

      typedef boost::make_variant_over<QF_BV_Tags>::type QF_BV_Tag;

      } // namespace metaSMT::logic::QF_BV::tag
    } // namespace metaSMT::logic::QF_BV
  } // namespace metaSMT::logic
} // namespace metaSMT
#endif // HEADER_metaSMT_TAG_QF_BV_HPP
//  vim: ft=cpp:ts=2:sw=2:expandtab
