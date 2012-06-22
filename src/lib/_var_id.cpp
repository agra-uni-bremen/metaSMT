#include "../metaSMT/impl/_var_id.hpp"

namespace metaSMT {
  namespace impl {
      unsigned new_var_id(  )
      {
        static unsigned _id = 0;
        ++_id;
        return _id;
      } 
  } /* impl */
} /* metaSMT */
