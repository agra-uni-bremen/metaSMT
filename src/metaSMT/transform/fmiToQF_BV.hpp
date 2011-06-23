#pragma once

#include "../frontend/QF_BV.hpp"
#include <boost/proto/transform.hpp>
#include "rewrite.hpp"


namespace metaSMT {
  namespace transform {
    namespace proto = boost::proto;

    struct fmiToQF_BV;

    struct fmiToQF_BV_c
    {
      // The primary template matches nothing:
      template<typename Tag>
        struct case_
        : proto::nary_expr<proto::_, proto::vararg<fmiToQF_BV> >
        {};
    };

    template<>
    struct fmiToQF_BV_c::case_<proto::tag::terminal>
      : proto::_ 
    {};

    struct make_bvand: proto::callable
    {
        template<typename Sig>
        struct result;
    
        template<typename This, typename Left, typename Right>
        struct result<This(Left, Right)>
        // this class provides ::type
        : boost::proto::result_of::make_expr< 
              logic::QF_BV::tag::bvand_tag
            , logic::QF_BV::QF_BV_Domain
            , Left
            , Right
          >
        {};
    
        template<typename Left, typename Right>
        typename make_bvand::result<make_bvand(Left,Right)>::type 
        operator()(Left const & left, Right const & right) const
        {
            return boost::proto::make_expr<logic::QF_BV::tag::bvand_tag, logic::QF_BV::QF_BV_Domain>( left, right);
        }
    };

   
#define TRANSLATE_FMI_QF_BV( tag1, tag2) \
    template<>\
    struct fmiToQF_BV_c::case_<tag1>\
      : proto::call< \
          proto::functional::make_expr<tag2>( \
                fmiToQF_BV(proto::_left)\
              , fmiToQF_BV(proto::_right)\
            )>\
    {};

    TRANSLATE_FMI_QF_BV( proto::tag::bitwise_and,    logic::QF_BV::tag::bvand_tag)
    TRANSLATE_FMI_QF_BV( proto::tag::bitwise_or,     logic::QF_BV::tag::bvor_tag)
    TRANSLATE_FMI_QF_BV( proto::tag::bitwise_xor,    logic::QF_BV::tag::bvxor_tag)
    TRANSLATE_FMI_QF_BV( proto::tag::equal_to,       logic::tag::equal_tag)
    TRANSLATE_FMI_QF_BV( proto::tag::not_equal_to,   logic::tag::nequal_tag)
    TRANSLATE_FMI_QF_BV( proto::tag::modulus_assign, logic::tag::equal_tag)
    TRANSLATE_FMI_QF_BV( proto::tag::shift_left,     logic::QF_BV::tag::bvshl_tag)
    TRANSLATE_FMI_QF_BV( proto::tag::shift_right,    logic::QF_BV::tag::bvshr_tag)

    TRANSLATE_FMI_QF_BV( proto::tag::plus,           logic::QF_BV::tag::bvadd_tag)
    TRANSLATE_FMI_QF_BV( proto::tag::multiplies,     logic::QF_BV::tag::bvmul_tag)
    TRANSLATE_FMI_QF_BV( proto::tag::minus,          logic::QF_BV::tag::bvsub_tag)
    TRANSLATE_FMI_QF_BV( proto::tag::divides,        logic::QF_BV::tag::bvudiv_tag)
    TRANSLATE_FMI_QF_BV( proto::tag::modulus,        logic::QF_BV::tag::bvurem_tag)

#undef TRANSLATE_FMI_QF_BV

    template<>
    struct fmiToQF_BV_c::case_<proto::tag::complement>
      : proto::call<
          proto::functional::make_expr<logic::QF_BV::tag::bvnot_tag>(
                fmiToQF_BV(proto::_left)
            )>
    {};

    template<>
    struct fmiToQF_BV_c::case_<proto::tag::negate>
      : proto::call<
          proto::functional::make_expr<logic::QF_BV::tag::bvneg_tag>(
                fmiToQF_BV(proto::_left)
            )>
    {};

    struct fmiToQF_BV : proto::switch_< fmiToQF_BV_c > {};
  
  } /* transform */
} /* metaSMT */


// vim: tabstop=2 shiftwidth=2 expandtab
