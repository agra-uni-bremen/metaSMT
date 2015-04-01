#include "../metaSMT/impl/_var_id.hpp"

#include <boost/atomic.hpp>

namespace metaSMT {
  namespace impl {
      unsigned new_var_id(  )
      {
        static boost::atomic_uint _id ( 0u );
        ++_id;
        return _id;
      } 
  } /* impl */
} /* metaSMT */
