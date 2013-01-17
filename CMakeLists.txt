PROJECT(metaSMT)

cmake_minimum_required(VERSION 2.8.2)
include(CheckIncludeFileCXX)
if(CMAKE_VERSION VERSION_LESS 2.8.3)
  include(cmake/feature_summary_stub.cmake)
else()
  include(FeatureSummary)
endif()

include(CTest)

set(CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/cmake/Modules )

set(Boost_NO_BOOST_CMAKE true)
set(Boost_NO_SYSTEM_PATHS true)
set(Boost_ADDITIONAL_VERSIONS "1.50.0")
find_package(Boost COMPONENTS iostreams thread system python)

if(NOT ${Boost_FOUND})
  message(FATAL_ERROR "Boost could not be found.")
endif()

set_package_info(Boost "Portable C++ libraries")
include_directories(${Boost_INCLUDE_DIRS})

list(INSERT CMAKE_PREFIX_PATH 0 "${CMAKE_SOURCE_DIR}/cmake")

# Set the default version number, but try to calculate
# a proper version from git.
SET(metaSMT_VERSION 4)
include(cmake/get_git_version.cmake)

include(cmake/build_type.cmake)
include(cmake/default_compliler_flags.cmake)
include(cmake/config_file.cmake)

###  
# Options to force disable certain solvers. 
# set all solvers to "on" with good support and experimental or
# work in progress to "off"
###
option(metaSMT_USE_SMT2       "try to use SMTLIB2 solver" on)
option(metaSMT_USE_SWORD      "try to use SWORD solver" on)
option(metaSMT_USE_Boolector  "try to use Boolector solver" on)
option(metaSMT_USE_Z3         "try to use Z3 solver" on)
option(metaSMT_USE_STP        "try to use STP solver" on)
option(metaSMT_USE_CUDD       "try to use CUDD BDD package" on )
option(metaSMT_USE_MiniSat    "try to use minisat SAT solver" on)  
option(metaSMT_USE_picosat    "try to use picosat SAT solver" on)
option(metaSMT_USE_Aiger      "try to use aiger" on)
option(metaSMT_USE_CW         "try to use clause writers" on)
option(metaSMT_USE_ExprSolver "try to use expression solver" on)

option(metaSMT_DOC_Doxygen    "try to build doxygen documentation" off)
option(metaSMT_ENABLE_TESTS   "build tests (recommended)" on)
option(metaSMT_ENABLE_BINDINGS "build bindings" on)
option(metaSMT_ENABLE_TOOLBOX "build toolbox projects" on)

set(metaSMT_CONFIG_DIR "share/metaSMT" CACHE PATH 
  "where to install CMake and Make Config files")

if ( NOT TIMEOUT )
  set(TIMEOUT 5 CACHE STRING "The timeout for tests")
endif()


if(metaSMT_USE_SWORD)
  find_package(SWORD QUIET)
else(metaSMT_USE_SWORD)
  set(SWORD_FOUND 0)
endif(metaSMT_USE_SWORD)
set_package_info(SWORD "solver for SMT QF_BV")

if(metaSMT_USE_Boolector)
  find_package(Boolector QUIET)
  list(APPEND Boolector_INCLUDE_DIR ${boolector_INCLUDE_DIRS})
  list(APPEND Boolector_LIBRARIES ${boolector_LIBRARIES})
else(metaSMT_USE_Boolector)
  set(Boolector_FOUND 0)
endif(metaSMT_USE_Boolector)
set_package_info(Boolector "solver for SMT QF_BV and Arrays")

if (metaSMT_USE_Z3)
	find_package(Z3 QUIET)
else(metaSMT_USE_Z3)
  set(Z3_FOUND 0)
endif(metaSMT_USE_Z3)
set_package_info(Z3 "solver for various SMT theories")

if(metaSMT_USE_STP)
  find_package(STP QUIET)
else(metaSMT_USE_STP)
  set(STP_FOUND 0)
endif(metaSMT_USE_STP)
set_package_info(STP "solver for SMT QF_BV and Arrays")

if (metaSMT_USE_CUDD)
  find_package(CUDD QUIET)
else (metaSMT_USE_CUDD)
  set(CUDD_FOUND 0)
endif (metaSMT_USE_CUDD)
set_package_info(CUDD "binary decision diagrams")

if (metaSMT_USE_Aiger)
  find_package(Aiger QUIET) 
  list(APPEND Aiger_LIBRARIES Aiger)
else (metaSMT_USE_Aiger)
  set(Aiger_FOUND 0)
endif(metaSMT_USE_Aiger)
set_package_info(Aiger "And Inverter Graph libraries")

if (metaSMT_USE_MiniSat)
  find_package(MiniSat QUIET)
else (metaSMT_USE_MiniSat)
  set(MiniSat_FOUND 0)
endif (metaSMT_USE_MiniSat)
set_package_info(MiniSat "SAT solver MiniSAT")

if (metaSMT_USE_picosat )
  find_package (PicoSAT QUIET)
endif(metaSMT_USE_picosat )
set_package_info(PicoSat "SAT solver PicoSat")

find_package(GMP QUIET)
set_package_info(GMP "optional, required by some backends")
if(NOT GMP_FOUND)
  find_library(GMP_LIBRARIES gmp PATHS ${GMP_DIR})
  find_library(GMPXX_LIBRARIES gmpxx PATHS ${GMP_DIR})
else(NOT GMP_FOUND)
  set(GMP_LIBRARIES "")
  set(GMPXX_LIBRARIES "")
endif(NOT GMP_FOUND)

find_package(OMP QUIET)
set_package_info(OMP "optional, required by some backends")
## later versions of GMP link against libomp
if(NOT OMP_FOUND)
  find_library(OMP_LIBRARIES gomp PATHS ${OMP_DIR})
else(NOT OMP_FOUND)
  set(OMP_LIBRARIES "")
endif(NOT OMP_FOUND)

if(Z3_FOUND)
  if( GMPXX_LIBRARIES )
    set(Z3_LIBRARIES ${Z3_LIBRARIES} ${GMPXX_LIBRARIES})
  else ()
    set(Z3_LIBRARIES ${Z3_LIBRARIES} gmpxx)
  endif()

  if( GMP_LIBRARIES )
    set(Z3_LIBRARIES ${Z3_LIBRARIES} ${GMP_LIBRARIES})
  else ()
    set(Z3_LIBRARIES ${Z3_LIBRARIES} gmp)
  endif()

  if( OMP_LIBRARIES )
    set(Z3_LIBRARIES ${Z3_LIBRARIES} ${OMP_LIBRARIES})
  else ()
    set(Z3_LIBRARIES ${Z3_LIBRARIES} gomp)
  endif()

  include(CheckCXXSourceRuns)

  set(CMAKE_REQUIRED_INCLUDES ${Z3_INCLUDE_DIR})
  set(CMAKE_REQUIRED_LIBRARIES ${Z3_LIBRARIES})

  check_CXX_source_runs("#include <z3++.h>
int main(int argc, const char *argv[]) {
  z3::context c;
  z3::solver s(c);
  s.check();
  return 0;
}"
  Z3_WORKS)

  if( NOT Z3_WORKS )
    message(WARNING "Disabling Z3. A version of Z3 >= 4.0 is required.")
    set( Z3_FOUND 0)
  endif()
endif()

if (metaSMT_DOC_Doxygen)
  find_package(Doxygen)
else (metaSMT_DOC_Doxygen)
  set(Doxygen_FOUND 0)
endif (metaSMT_DOC_Doxygen)



if(SWORD_FOUND)
  config_find(SWORD ${SWORD_DIR})
  list(APPEND metaSMT_LIBS ${SWORD_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${SWORD_INCLUDE_DIR})
endif(SWORD_FOUND)

if(Boolector_FOUND)
  config_find(Boolector ${Boolector_DIR})
  list(APPEND metaSMT_LIBS ${Boolector_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${Boolector_INCLUDE_DIR})
endif(Boolector_FOUND)

if(Z3_FOUND)
  config_find(Z3 ${Z3_DIR})
  list(APPEND metaSMT_LIBS ${Z3_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${Z3_INCLUDE_DIR})
endif(Z3_FOUND)

if(STP_FOUND)
  config_find(STP ${STP_DIR})
  list(APPEND metaSMT_LIBS ${STP_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${STP_INCLUDE_DIR})
endif(STP_FOUND)

if(Aiger_FOUND)
  config_find(Aiger ${Aiger_DIR})
  list(APPEND metaSMT_LIBS ${Aiger_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${Aiger_INCLUDE_DIR})
endif(Aiger_FOUND)

if(CUDD_FOUND)
  config_find(CUDD ${CUDD_DIR})
  list(APPEND metaSMT_LIBS CUDD_obj )
  list(APPEND metaSMT_INCLUDES ${CUDD_INCLUDE_DIR} ${cudd_INCLUDE_DIRS})
endif(CUDD_FOUND)

if(MiniSat_FOUND)
  config_find(MiniSat ${MiniSat_DIR})
  list(APPEND metaSMT_LIBS MiniSat_libMiniSat)
  list(APPEND metaSMT_INCLUDES ${MiniSat_INCLUDE_DIR})
  list(APPEND metaSMT_CXXFLAGS "${MiniSat_CXXFLAGS}")
endif(MiniSat_FOUND)

if (PicoSAT_FOUND)
  config_find(PicoSAT ${PicoSAT_DIR})
  list(APPEND metaSMT_LIBS ${PicoSAT_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${PicoSAT_INCLUDE_DIR})
endif (PicoSAT_FOUND)

if( Boost_IOSTREAMS_FOUND )
  list(APPEND metaSMT_LIBS ${Boost_IOSTREAMS_LIBRARY})
endif()

if( Boost_THREAD_FOUND )
  list(APPEND metaSMT_LIBS ${Boost_THREAD_LIBRARY})
endif()

if( Boost_SYSTEM_FOUND )
  list(APPEND metaSMT_LIBS ${Boost_SYSTEM_LIBRARY})
endif()

############################################################
############# RPATH ########################################
############################################################

include(cmake/library_rpath.cmake)
add_dependent_libraries(${metaSMT_LIBS})


############################################################
############# subdirectories ###############################
############################################################

add_subdirectory(src)
add_subdirectory(doc)

if(metaSMT_ENABLE_TESTS)
  enable_testing()
  add_subdirectory(tests)
endif(metaSMT_ENABLE_TESTS)

if(metaSMT_ENABLE_BINDINGS)
  add_subdirectory(bindings)
endif(metaSMT_ENABLE_BINDINGS)

if(metaSMT_ENABLE_TOOLBOX)
  add_subdirectory(toolbox)
endif()

############################################################
########## generate cmake config files #####################
############################################################

generate_config_files()

Feature_Summary(WHAT ALL)

############################################################
##                CPack settings                          ##
############################################################


# CPack version numbers for release tarball name.
set(CPACK_PACKAGE_VERSION_MAJOR ${metaSMT_VERSION})
#set(CPACK_PACKAGE_VERSION_MINOR 0)
#set(CPACK_PACKAGE_VERSION_PATCH 0)

set(CPACK_PACKAGE_DESCRIPTION_SUMMARY "SMT programming library")
set(CPACK_PACKAGE_VENDOR "metaSMT development team")
set(CPACK_PACKAGE_DESCRIPTION_FILE ${CMAKE_CURRENT_SOURCE_DIR}/README)
set(CPACK_GENERATOR TGZ)
set(
CPACK_SOURCE_PACKAGE_FILE_NAME
"metaSMT-${metaSMT_VERSION}"
CACHE INTERNAL "tarball basename"
)
set(CPACK_SOURCE_GENERATOR TGZ TBZ2)

set(CPACK_SOURCE_IGNORE_FILES
"/\\\\.git"
"/deps"
"/build.*/"
"/root"
)
include(CPack)


############################################################
############################################################

# vim: ft=cmake:ts=2:sw=2:expandtab
