#pragma once

#include "Logic.hpp"
#include "QF_BV.hpp"
#include "Array.hpp"

#include <boost/mpl/joint_view.hpp>
#include <boost/mpl/copy.hpp>
#include <boost/mpl/size.hpp>

namespace metaSMT {

  namespace _all_logic_tags {
    typedef boost::mpl::joint_view< 
        logic::tag::Predicate_Tags
      , logic::QF_BV::tag::QF_BV_Tags 
      >::type all_Tags1;

    typedef boost::mpl::joint_view< 
        all_Tags1
      , logic::Array::tag::Array_Tags 
      >::type all_Tags2;

    typedef boost::mpl::copy<
       all_Tags2
       , boost::mpl::back_inserter< boost::mpl::vector<> >
      >::type all_Tags;
    //BOOST_MPL_ASSERT_RELATION( boost::mpl::size<allTags>::value, ==, 1 );
  }


  typedef boost::make_variant_over< _all_logic_tags::all_Tags >::type Tag;

} // namespace metaSMT

//  vim: ft=cpp:ts=2:sw=2:expandtab
