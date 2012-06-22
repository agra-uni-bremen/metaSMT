#pragma once
#include <string>

namespace metaSMT {
  namespace support {
    std::string find_executable( std::string const & progname
                               , std::string const & envname) 
    {
      char* env = getenv(envname.c_str());
      if(env) return env;
      return progname;
    }
  } /* support */
} /* metaSMT */

