#pragma once

#include <boost/mpl/bool.hpp>

namespace metaSMT {
  namespace features {

  /**
   *  This template provides a compile-time way
   *  to check for supported features of specific contexts.
   *  e.g. to declare native supported apis.
   *
   **/
  template <typename Context, typename Feature>
  struct supports : boost::mpl::false_ {};
  
  } /* features */
} /* metaSMT */
