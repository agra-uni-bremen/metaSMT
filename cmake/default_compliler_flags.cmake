#
# Add default C/CXX flags to reduce memory consumption and compile time with gcc
#

if( CMAKE_COMPILER_IS_GNUCC AND NOT CMAKE_C_FLAGS)
  set( CMAKE_C_FLAGS "--param ggc-min-expand=30 --param ggc-min-heapsize=8192" CACHE STRING "Flags used by the compiler during all build types." FORCE )
endif()

if( CMAKE_COMPILER_IS_GNUCXX AND NOT CMAKE_CXX_FLAGS)
  set( CMAKE_CXX_FLAGS "--param ggc-min-expand=30 --param ggc-min-heapsize=8192" CACHE STRING "Flags used by the compiler during all build types." FORCE )
endif()
