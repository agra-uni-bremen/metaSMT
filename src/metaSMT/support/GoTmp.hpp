#pragma once

#include <boost/filesystem.hpp>


namespace metaSMT {

  struct GoTmp {
    GoTmp ()
    : prevPath(boost::filesystem::current_path())
    , path()
    {

      if ( tryDir("/dev/shm") ) {
        // we are done, use ramdisk
      } else if( tryDir( boost::filesystem::temp_directory_path()) ) {
        // done, use /tmp
      } else {
        // currend dir should always work
        tryDir( prevPath );
      }
      boost::filesystem::current_path(path);

    }
  
    ~GoTmp() {
      boost::filesystem::current_path(prevPath);
      boost::filesystem::remove_all(path);
    }

    private:
      bool tryDir(boost::filesystem::path dir) {
        try {
          if (is_directory(dir)) {
            dir /= "metaSMT-%%%%%%";
            boost::filesystem::create_directory(path);
            return true;
          } 
        } catch (std::exception &) {
          // fallback to false
        }
        return false;
      }

    private:
      boost::filesystem::path prevPath;
      boost::filesystem::path path;
  };

} /* metaSMT */
