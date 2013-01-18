#pragma once

#include "string_concat.hpp"
#include "../tags/Logics.hpp"
#include <boost/mpl/map/map50.hpp>
#include <boost/mpl/string.hpp>
#include <boost/utility/enable_if.hpp>

namespace metaSMT {

  namespace predtags = ::metaSMT::logic::tag;
  namespace bvtags = ::metaSMT::logic::QF_BV::tag;
  namespace arraytags = ::metaSMT::logic::Array::tag;
  namespace mpl = boost::mpl;

  /** \cond **/
  typedef mpl::map46<
      mpl::pair<predtags::true_tag,    mpl::string<'t', 'r', 'u', 'e'> >
    , mpl::pair<predtags::false_tag,   mpl::string<'f', 'a', 'l', 's', 'e'> >
    , mpl::pair<bvtags::bvult_tag,     mpl::string<'b', 'v', 'u', 'l', 't'> >
    , mpl::pair<bvtags::bvneg_tag,     mpl::string<'b', 'v', 'n', 'e', 'g'> >
    , mpl::pair<bvtags::bvnot_tag,     mpl::string<'b', 'v', 'n', 'o', 't'> >

    , mpl::pair<bvtags::bvand_tag,     mpl::string<'b', 'v', 'a', 'n', 'd'> >
    , mpl::pair<bvtags::bvor_tag,      mpl::string<'b', 'v', 'o', 'r'> >
    , mpl::pair<bvtags::bvnand_tag,    mpl::string<'b', 'v', 'n', 'a', 'n', 'd'> >
    , mpl::pair<bvtags::bvnor_tag,     mpl::string<'b', 'v', 'n', 'o', 'r'> >
    , mpl::pair<bvtags::bvxor_tag,     mpl::string<'b', 'v', 'x', 'o', 'r'> >

    , mpl::pair<bvtags::bvxnor_tag,    mpl::string<'b', 'v', 'x', 'n', 'o', 'r'> >
    , mpl::pair<bvtags::bvadd_tag,     mpl::string<'b', 'v', 'a', 'd', 'd'> >
    , mpl::pair<bvtags::bvsub_tag,     mpl::string<'b', 'v', 's', 'u', 'b'> >
    , mpl::pair<bvtags::bvmul_tag,     mpl::string<'b', 'v', 'm', 'u', 'l'> >
    , mpl::pair<bvtags::bvudiv_tag,    mpl::string<'b', 'v', 'u', 'd', 'i', 'v'> >
    , mpl::pair<bvtags::bvsrem_tag,    mpl::string<'b', 'v', 's', 'r', 'e', 'm'> >
    , mpl::pair<bvtags::bvsdiv_tag,    mpl::string<'b', 'v', 's', 'd', 'i', 'v'> >
    , mpl::pair<bvtags::bvurem_tag,    mpl::string<'b', 'v', 'u', 'r', 'e', 'm'> >
    , mpl::pair<bvtags::bvsle_tag,     mpl::string<'b', 'v', 's', 'l', 'e'> >

    , mpl::pair<bvtags::bvslt_tag,     mpl::string<'b', 'v', 's', 'l', 't'> >
    , mpl::pair<bvtags::bvsge_tag,     mpl::string<'b', 'v', 's', 'g', 'e'> >    
    , mpl::pair<bvtags::bvsgt_tag,     mpl::string<'b', 'v', 's', 'g', 't'> >
    , mpl::pair<bvtags::bvule_tag,     mpl::string<'b', 'v', 'u', 'l', 'e'> >
    , mpl::pair<bvtags::bvult_tag,     mpl::string<'b', 'v', 'u', 'l', 't'> >

    , mpl::pair<bvtags::bvuge_tag,     mpl::string<'b', 'v', 'u', 'g', 'e'> >
    , mpl::pair<bvtags::bvugt_tag,     mpl::string<'b', 'v', 'u', 'g', 't'> >
    , mpl::pair<predtags::implies_tag, mpl::string<'=', '>'> >
    , mpl::pair<predtags::equal_tag,   mpl::string<'='> >
    , mpl::pair<predtags::xor_tag,     mpl::string<'x', 'o', 'r'> >

    , mpl::pair<predtags::and_tag,     mpl::string<'a', 'n', 'd'> >
    , mpl::pair<predtags::or_tag,      mpl::string<'o', 'r'> >
    , mpl::pair<bvtags::bit0_tag,      mpl::string<'b', 'i', 't', '0'> >
    , mpl::pair<bvtags::bit1_tag,      mpl::string<'b', 'i', 't', '1'> >
    , mpl::pair<predtags::ite_tag,     mpl::string<'i', 't', 'e'> >

    , mpl::pair<predtags::not_tag,     mpl::string<'n', 'o', 't'> >
    , mpl::pair<bvtags::bvcomp_tag,    mpl::string<'b', 'v', 'c', 'o', 'm', 'p'> >
    , mpl::pair<bvtags::concat_tag,    mpl::string<'c', 'o', 'n', 'c', 'a', 't'> >
    , mpl::pair<arraytags::select_tag, mpl::string<'s', 'e', 'l', 'e', 'c', 't'> >
    , mpl::pair<arraytags::store_tag,  mpl::string<'s', 't', 'o', 'r', 'e'> >
    , mpl::pair<bvtags::bvshl_tag,     mpl::string<'b', 'v', 's', 'h', 'l'> >    
    , mpl::pair<bvtags::bvshr_tag,     mpl::string<'b', 'v', 'l', 's', 'h', 'r'> >    
    , mpl::pair<bvtags::bvashr_tag,    mpl::string<'b', 'v', 'a', 's', 'h', 'r'> >    

    , mpl::pair<bvtags::extract_tag,      mpl::string<'e', 'x', 't', 'r', 'a', 'c', 't'> >
    , mpl::pair<bvtags::repeat_tag,       mpl::string<'r', 'e', 'p', 'e', 'a', 't'> >
    , mpl::pair<bvtags::zero_extend_tag,  string_concat<
                                            mpl::string<'z', 'e', 'r', 'o', '_'>,
                                            mpl::string<'e', 'x', 't', 'e', 'n', 'd'>
                                          >::type >
    , mpl::pair<bvtags::sign_extend_tag,  string_concat<
                                            mpl::string<'s', 'i', 'g', 'n', '_'>,
                                            mpl::string<'e', 'x', 't', 'e', 'n', 'd'>
                                          >::type >
  > SMT_NameMap;
  /** \endcond **/


  template<typename Tag> 
  inline typename boost::enable_if<
      typename mpl::has_key< SMT_NameMap, Tag>::type
    , std::string
    >::type
  get_tag_name(Tag const &t) {
    typedef typename mpl::at< SMT_NameMap, Tag >::type name;
    return mpl::c_str<name>::value;
  }

  template<typename Tag> 
  inline typename boost::disable_if<
      typename mpl::has_key< SMT_NameMap, Tag>::type
    , std::string
    >::type
  get_tag_name(Tag const &t) {
    return "unknown_name";
  }


  typedef mpl::map7<
      mpl::pair<predtags::nequal_tag, mpl::pair<predtags::not_tag, predtags::equal_tag > >
    , mpl::pair<predtags::nand_tag, mpl::pair<predtags::not_tag, predtags::and_tag > >
    , mpl::pair<predtags::nor_tag, mpl::pair<predtags::not_tag, predtags::or_tag > >
    , mpl::pair<predtags::xnor_tag, mpl::pair<predtags::not_tag, predtags::xor_tag > >
    , mpl::pair<bvtags::bvnand_tag, mpl::pair<bvtags::bvnot_tag, bvtags::bvand_tag > >
    , mpl::pair<bvtags::bvnor_tag, mpl::pair<bvtags::bvnot_tag, bvtags::bvor_tag > >
    , mpl::pair<bvtags::bvxnor_tag, mpl::pair<bvtags::bvnot_tag, bvtags::bvxor_tag > >
  > SMT_Negated_Map;



} // metaSMT
