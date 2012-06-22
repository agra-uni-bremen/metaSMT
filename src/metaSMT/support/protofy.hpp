#pragma once
#include <boost/proto/core.hpp>

namespace metaSMT {
  namespace detail {

    template<typename T>
    typename boost::disable_if<proto::is_expr<T>, proto::literal<T> >::type 
    protofy ( T e) {
      return proto::lit(e);
    }

    template<typename T>
    typename boost::enable_if<proto::is_expr<T>, T>::type 
    protofy ( T e) {
      return e;
    }
  
  }
} /* metaSMT */
