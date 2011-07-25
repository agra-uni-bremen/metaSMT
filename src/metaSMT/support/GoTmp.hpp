#pragma once
#include <cstdlib>
#include <cstring>
#include <sys/stat.h>
#include <ftw.h>

namespace metaSMT {

  struct GoTmp {
    GoTmp ()
    : prevPath(get_current_dir_name())
    , path( (char*) malloc(1025) )
    {
      struct stat st;
      if(stat("/dev/shm",&st) == 0) {
        strncpy(path, "/dev/shm/metaSMT-XXXXXX", 1025);
        mkdtemp(path);
      } else if(stat("/tmp",&st) == 0) {
        strncpy(path, "/tmp/metaSMT-XXXXXX", 1025);
        mkdtemp(path);
      } 
      chdir(path);
    }
  
    ~GoTmp() {
      chdir(prevPath);
  
      recursive_delete(path);
  
      free(path);
      free(prevPath);
    }

    static int recursive_deleter(const char * path, const struct stat *, int type, struct FTW *){
      switch (type) {
        case FTW_D:
        case FTW_DP:
        case FTW_DNR:
          return rmdir(path);
        case FTW_F:
        case FTW_NS:
        case FTW_SL:
        case FTW_SLN:
          return unlink(path);
      }
      return 1;
    }
    static int recursive_delete (const char* path) {

      return nftw( path, recursive_deleter, 20, FTW_DEPTH|FTW_PHYS|FTW_MOUNT);
    }
  
    char* prevPath;
    char* path;
  };

} /* metaSMT */
