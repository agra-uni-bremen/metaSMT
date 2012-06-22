#pragma once
#include <boost/proto/core.hpp>

namespace metaSMT {
  namespace transform {

    template<typename Domain>
    struct rewrite1 {
      template<typename Tag, typename Child>
      struct to
      : boost::proto::result_of::make_expr< Tag, Domain, Child> 
      {};
    };

    template<typename Domain>
    struct rewrite2 {
      template<typename Tag, typename Left, typename Right>
      struct to
      : boost::proto::result_of::make_expr< Tag, Domain, Left, Right> 
      {};
    };
    	
  } /* transform */
} /* metaSMT */


// vim: tabstop=2 shiftwidth=2 expandtab
