PROJECT(metaSMT)
cmake_minimum_required(VERSION 2.8.9)

include(CheckIncludeFileCXX)
include(FeatureSummary)

include(CTest)

set(CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/cmake/Modules )

set(Boost_NO_BOOST_CMAKE true)
set(Boost_NO_SYSTEM_PATHS true)
set(Boost_ADDITIONAL_VERSIONS "1.50.0")
find_package(Boost COMPONENTS iostreams thread system python filesystem)

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
option(metaSMT_USE_CVC4        "try to use CVC4 solver" on)
option(metaSMT_USE_CUDD       "try to use CUDD BDD package" on )
option(metaSMT_USE_MiniSat    "try to use minisat SAT solver" on)  
option(metaSMT_USE_picosat    "try to use picosat SAT solver" on)
option(metaSMT_USE_lingeling  "try to use lingeling SAT solver" on)
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


if(metaSMT_USE_SWORD AND NOT APPLE)
  find_package(SWORD QUIET)
else()
  set(SWORD_FOUND 0)
endif()
set_package_info(SWORD "solver for SMT QF_BV")

if(metaSMT_USE_Boolector)
  find_package(Boolector QUIET)
  list(APPEND Boolector_INCLUDE_DIR ${boolector_INCLUDE_DIRS})
  list(APPEND Boolector_LIBRARIES ${boolector_LIBRARIES})
else()
  set(Boolector_FOUND 0)
endif()
set_package_info(Boolector "solver for SMT QF_BV and Arrays")

if (metaSMT_USE_Z3)
	find_package(Z3 QUIET)
else()
  set(Z3_FOUND 0)
endif()
set_package_info(Z3 "solver for various SMT theories")

if(metaSMT_USE_STP)
  find_package(STP QUIET)
  find_package(cryptominisat4 QUIET)
else()
  set(STP_FOUND 0)
endif()
set_package_info(STP "solver for SMT QF_BV and Arrays")

if(metaSMT_USE_CVC4)
  find_package(CVC4 QUIET)
else()
  set(CVC4_FOUND 0)
endif()
set_package_info(CVC4 "solver for various SMT theories")

if (metaSMT_USE_CUDD)
  find_package(CUDD QUIET)
else ()
  set(CUDD_FOUND 0)
endif ()
set_package_info(CUDD "binary decision diagrams")

if (metaSMT_USE_Aiger)
  find_package(Aiger QUIET) 
  list(APPEND Aiger_LIBRARIES Aiger)
else ()
  set(Aiger_FOUND 0)
endif()
set_package_info(Aiger "And Inverter Graph libraries")

if (metaSMT_USE_MiniSat)
  find_package(MiniSat QUIET)
else ()
  set(MiniSat_FOUND 0)
endif ()
set_package_info(MiniSat "SAT solver MiniSAT")

if (metaSMT_USE_picosat )
  find_package (PicoSAT QUIET)
endif()
set_package_info(PicoSat "SAT solver PicoSat")

if( metaSMT_USE_lingeling )
  find_package( Lingeling QUIET)
endif()
set_package_info(Lingeling "SAT solver lingeling")

find_package(GMP QUIET)
set_package_info(GMP "optional, required by some backends")
if(NOT GMP_FOUND)
  find_library(GMP_LIBRARIES gmp PATHS ${GMP_DIR})
  find_library(GMPXX_LIBRARIES gmpxx PATHS ${GMP_DIR})
else()
  set(GMP_LIBRARIES "")
  set(GMPXX_LIBRARIES "")
endif()

find_package(OMP QUIET)
set_package_info(OMP "optional, required by some backends")
## later versions of GMP link against libomp
if(NOT OMP_FOUND)
  find_library(OMP_LIBRARIES gomp PATHS ${OMP_DIR})
else()
  set(OMP_LIBRARIES "")
endif()

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

  set(Z3_LIBRARIES ${Z3_LIBRARIES} rt pthread)

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

if(CVC4_FOUND)
  if( GMPXX_LIBRARIES )
    set(CVC4_LIBRARIES ${CVC4_LIBRARIES} ${GMPXX_LIBRARIES})
  else ()
    set(CVC4_LIBRARIES ${CVC4_LIBRARIES} gmpxx)
  endif()

  if( GMP_LIBRARIES )
    set(CVC4_LIBRARIES ${CVC4_LIBRARIES} ${GMP_LIBRARIES})
  else ()
    set(CVC4_LIBRARIES ${CVC4_LIBRARIES} gmp)
  endif()

endif()


if (metaSMT_DOC_Doxygen)
  find_package(Doxygen)
else ()
  set(Doxygen_FOUND 0)
endif ()



if(SWORD_FOUND)
  config_find(SWORD ${SWORD_DIR})
  list(APPEND metaSMT_LIBS ${SWORD_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${SWORD_INCLUDE_DIR})
endif()

if(Boolector_FOUND)
  config_find(Boolector ${Boolector_DIR})
  list(APPEND metaSMT_LIBS ${Boolector_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${Boolector_INCLUDE_DIR})
endif()

if(Z3_FOUND)
  config_find(Z3 ${Z3_DIR})
  list(APPEND metaSMT_LIBS ${Z3_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${Z3_INCLUDE_DIR})
endif()

if(STP_FOUND AND cryptominisat4_FOUND)
  config_find(STP ${STP_DIR})
  config_find(cryptominisat4 ${cryptominisat4_DIR})
  message( STATUS "STP_LIBRARIES: ${STP_SHARED_LIBRARY} ${CRYPTOMINISAT4_LIBRARIES}" )
  list(APPEND metaSMT_LIBS ${STP_SHARED_LIBRARY} ${CRYPTOMINISAT4_LIBRARIES})
  message( STATUS "STP_INCLUDE_DIR: ${STP_INCLUDE_DIRS}" )
  list(APPEND metaSMT_INCLUDES ${STP_INCLUDE_DIRS})
else()
  set( STP_FOUND 0 )
endif()

if(CVC4_FOUND)
  config_find(CVC4 ${CVC4_DIR})
  list(APPEND metaSMT_LIBS ${CVC4_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${CVC4_INCLUDE_DIR})
endif()

if(Aiger_FOUND)
  config_find(Aiger ${Aiger_DIR})
  list(APPEND metaSMT_LIBS ${Aiger_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${Aiger_INCLUDE_DIR})
endif()

if(CUDD_FOUND)
  config_find(CUDD ${CUDD_DIR})
  list(APPEND metaSMT_LIBS CUDD_obj CUDD_cudd CUDD_dddmp CUDD_epd CUDD_mtr CUDD_st CUDD_util)
  list(APPEND metaSMT_INCLUDES ${CUDD_INCLUDE_DIR} ${cudd_INCLUDE_DIRS})
endif()

if(MiniSat_FOUND)
  config_find(MiniSat ${MiniSat_DIR})
  list(APPEND metaSMT_LIBS ${MiniSat_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${MiniSat_INCLUDE_DIR})
  list(APPEND metaSMT_CXXFLAGS "${MiniSat_CXXFLAGS}")
endif()

if (PicoSAT_FOUND)
  config_find(PicoSAT ${PicoSAT_DIR})
  list(APPEND metaSMT_LIBS ${PicoSAT_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${PicoSAT_INCLUDE_DIR})
endif ()

if (Lingeling_FOUND)
  config_find(Lingeling ${Lingeling_DIR})
  list(APPEND metaSMT_LIBS ${Lingeling_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${Lingeling_INCLUDE_DIR})
endif ()

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
endif()

if(metaSMT_ENABLE_BINDINGS)
  add_subdirectory(bindings)
endif()

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
set(CPACK_PACKAGE_DESCRIPTION_FILE ${CMAKE_CURRENT_SOURCE_DIR}/README.md)
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
