#
# Add the build_type "Profiling", that
# * enables gcov profiling
# * enables -Wall (all warnings)
# * disables optimizations
# for GCC or compatible compilers
#

SET( CMAKE_CXX_FLAGS_PROFILING "-O0 -g -Wall -fprofile-arcs -ftest-coverage" CACHE STRING
  "Flags used by the C++ compiler during profiling builds."
  FORCE )
SET( CMAKE_C_FLAGS_PROFILING "-O0 -g -Wall -fprofile-arcs -ftest-coverage" CACHE STRING
  "Flags used by the C compiler during profiling builds."
  FORCE )
SET( CMAKE_EXE_LINKER_FLAGS_PROFILING
  "-fprofile-arcs -ftest-coverage" CACHE STRING
  "Flags used for linking binaries during profiling builds."
  FORCE )
SET( CMAKE_SHARED_LINKER_FLAGS_PROFILING
  "-fprofile-arcs -ftest-coverage" CACHE STRING
  "Flags used by the shared libraries linker during profiling builds."
  FORCE )
MARK_AS_ADVANCED(
  CMAKE_CXX_FLAGS_PROFILING
  CMAKE_C_FLAGS_PROFILING
  CMAKE_EXE_LINKER_FLAGS_PROFILING
  CMAKE_SHARED_LINKER_FLAGS_PROFILING )
# Update the documentation string of CMAKE_BUILD_TYPE for GUIs
SET( CMAKE_BUILD_TYPE "${CMAKE_BUILD_TYPE}" CACHE STRING
  "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel Profiling."
  FORCE )

