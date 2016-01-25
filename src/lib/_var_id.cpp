#include "../metaSMT/impl/_var_id.hpp"
#include <boost/version.hpp>

#if BOOST_VERSION >= 105500

#include <boost/atomic.hpp>
unsigned metaSMT::impl::new_var_id()
{
  static boost::atomic_uint _id ( 0u );
  ++_id;
  return _id;
} 

#else

unsigned metaSMT::impl::new_var_id()
{
  static unsigned _id ( 0u );
  ++_id;
  return _id;
} 

#endif

