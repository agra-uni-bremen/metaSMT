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

    int execute(const std::string& file, const std::vector<std::string>& argv) {
      std::vector<const char*> av;
      for (std::vector<std::string>::const_iterator i = argv.begin(); i != argv.end(); ++i)
        av.push_back(i->c_str());
      av.push_back(static_cast<const char*>(0));
      return execvp(file.c_str(), const_cast<char * const* >(&av[0]));
    }
  } /* support */
} /* metaSMT */

