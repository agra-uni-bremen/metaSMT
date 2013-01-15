#pragma once
#include <string>
#include <unistd.h>

namespace metaSMT {
  namespace support {
    inline std::string find_executable( std::string const & progname
                               , std::string const & envname) 
    {
      char* env = getenv(envname.c_str());
      if(env) return env;
      return progname;
    }

    inline int execvp(std::string const &file,
                      std::vector<std::string> const &args) {
      std::vector<char const *> av;
      for ( std::vector<std::string>::const_iterator it = args.begin();
            it != args.end(); ++it )
        av.push_back( it->c_str() );
      av.push_back(0);
      return ::execvp(file.c_str(), const_cast<char * const *>(&av[0]));
    }
  } /* support */
} /* metaSMT */

