PROJECT(metaSMT)
SET(VERSION 0.1)

cmake_minimum_required(VERSION 2.8.2)
include(CheckIncludeFileCXX)
include(FeatureSummary)
include(CTest)

set(CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/cmake/Modules )

set(Boost_ADDITIONAL_VERSIONS "1.46.1")
find_package(Boost REQUIRED COMPONENTS iostreams)
set_package_info(Boost "Portable C++ libraries")
include_directories(${Boost_INCLUDE_DIRS})

list(INSERT CMAKE_PREFIX_PATH 0 "${CMAKE_SOURCE_DIR}/cmake")

SET( CMAKE_CXX_FLAGS_PROFILING "-O0 -g -Wall -fprofile-arcs -ftest-coverage" CACHE STRING
  "Flags used by the C++ compiler during maintainer builds."
  FORCE )
SET( CMAKE_C_FLAGS_PROFILING "-O0 -g -Wall -fprofile-arcs -ftest-coverage" CACHE STRING
  "Flags used by the C compiler during maintainer builds."
  FORCE )
SET( CMAKE_EXE_LINKER_FLAGS_PROFILING
  "-fprofile-arcs -ftest-coverage" CACHE STRING
  "Flags used for linking binaries during maintainer builds."
  FORCE )
SET( CMAKE_SHARED_LINKER_FLAGS_PROFILING
  "-fprofile-arcs -ftest-coverage" CACHE STRING
  "Flags used by the shared libraries linker during maintainer builds."
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

###  
# Options to force disable certain solvers. 
# set all solvers to "on" with good support and experimental or
# work in progress to "off"
###
option(metaSMT_USE_SWORD      "try to use SWORD solver" on)
option(metaSMT_USE_Boolector  "try to use Boolector solver" on)
option(metaSMT_USE_Z3         "try to use Z3 solver" on)
option(metaSMT_USE_CUDD       "try to use CUDD BDD package" on )
option(metaSMT_USE_mathsat    "try to use mathsat solver (incomplete)" off)
option(metaSMT_USE_MiniSat    "try to use minisat SAT solver" on)  
option(metaSMT_USE_picosat    "try to use picosat SAT solver" on)
option(metaSMT_USE_Aiger      "try to use aiger" on)

option(metaSMT_DOC_Doxygen    "try to build doxygen documentation" off)
option(metaSMT_ENABLE_TESTS   "build tests (recommended)" on)
option(metaSMT_ENABLE_TOOLBOX "build toolbox projects" on)

set(metaSMT_CONFIG_DIR "share/metaSMT" CACHE PATH 
  "where to install CMake and Make Config files")

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
  set(GMPXX_LIBRARIES "")
endif(NOT GMP_FOUND)

if(Z3_FOUND)
  set(Z3_LIBRARIES ${Z3_LIBRARIES} ${GMPXX_LIBRARIES} ${GMP_LIBRARIES})
endif(Z3_FOUND)

if (metaSMT_USE_mathsat)
  find_package(mathsat QUIET)
  if(NOT mathsat_FOUND)
    find_library(mathsat_LIBRARIES mathsat 
      DOC "path to mathsat library"
    )
    find_file(mathsat_H mathsat.h 
      HINTS include
      DOC "path to mathsat.h"
    )
    if(NOT mathsat_LIBRARIES OR NOT mathsat_H) 
      message(WARNING "mathsat was not found!")
    else(NOT mathsat_LIBRARIES OR NOT mathsat_H) 
      set(mathsat_FOUND 1)
    endif(NOT mathsat_LIBRARIES OR NOT mathsat_H) 
  
    set(mathsat_LIBRARIES ${mathsat_LIBRARIES} ${GMPXX_LIBRARIES} ${GMP_LIBRARIES})
  
    get_filename_component(mathsat_INCLUDE_DIR ${mathsat_H} PATH)
  endif(NOT mathsat_FOUND)
else (metaSMT_USE_mathsat)
  set(mathsat_FOUND 0)
endif (metaSMT_USE_mathsat)

if (metaSMT_DOC_Doxygen)
  find_package(Doxygen)
else (metaSMT_DOC_Doxygen)
  set(Doxygen_FOUND 0)
endif (metaSMT_DOC_Doxygen)



if(SWORD_FOUND)
  list(APPEND metaSMT_LIBS ${SWORD_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${SWORD_INCLUDE_DIR})
endif(SWORD_FOUND)

if(Boolector_FOUND)
  list(APPEND metaSMT_LIBS ${Boolector_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${Boolector_INCLUDE_DIR})
endif(Boolector_FOUND)

if(Z3_FOUND)
  list(APPEND metaSMT_LIBS ${Z3_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${Z3_INCLUDE_DIR})
endif(Z3_FOUND)

if(mathsat_FOUND)
  list(APPEND metaSMT_LIBS ${mathsat_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${mathsat_INCLUDE_DIR})
endif(mathsat_FOUND)

if(Aiger_FOUND)
  list(APPEND metaSMT_LIBS ${Aiger_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${Aiger_INCLUDE_DIR})
endif(Aiger_FOUND)

if(CUDD_FOUND)
  list(APPEND metaSMT_LIBS CUDD_obj )
  list(APPEND metaSMT_INCLUDES ${CUDD_INCLUDE_DIR} ${cudd_INCLUDE_DIRS})
endif(CUDD_FOUND)

if(MiniSat_FOUND)
  list(APPEND metaSMT_LIBS MiniSat_libMiniSat)
  list(APPEND metaSMT_INCLUDES ${MiniSat_INCLUDE_DIR})
  list(APPEND metaSMT_CXXFLAGS "${MiniSat_CXXFLAGS}")
endif(MiniSat_FOUND)

if (PicoSAT_FOUND)
  list(APPEND metaSMT_LIBS ${PicoSAT_LIBRARIES})
  list(APPEND metaSMT_INCLUDES ${PicoSAT_INCLUDE_DIR})
endif (PicoSAT_FOUND)

############################################################
############# subdirectories ###############################
############################################################

add_subdirectory(src)
add_subdirectory(doc)

if(metaSMT_ENABLE_TESTS)
  enable_testing()
  add_subdirectory(tests)
endif(metaSMT_ENABLE_TESTS)

if(metaSMT_ENABLE_TOOLBOX)
  add_subdirectory(toolbox)
endif()

############################################################

list(INSERT metaSMT_LIBS 0 ${CMAKE_INSTALL_PREFIX}/lib/libmetaSMT.a)
list(INSERT metaSMT_INCLUDES 0 ${CMAKE_INSTALL_PREFIX}/include)
## create metaSMT CMake config file
file(WRITE ${PROJECT_BINARY_DIR}/metaSMTConfig.cmake 
"set(metaSMT_FOUND 1)
set(metaSMT_INCLUDE_DIR ${metaSMT_INCLUDES})
get_filename_component(metaSMT_CONFIG_DIR "\${CMAKE_CURRENT_LIST_FILE}" PATH)
include("\${metaSMT_CONFIG_DIR}/metaSMT.cmake" )
set(metaSMT_CXXFLAGS \"${metaSMT_CXXFLAGS}\")
")
## create libmetaSMT config file for internal use
file(WRITE ${PROJECT_BINARY_DIR}/metaSMT.cmake 
"set(metaSMT_INCLUDE_DIR ${PROJECT_SOURCE_DIR}/src;${metaSMT_INCLUDES})\n"
)

## export target with install
INSTALL( FILES
  ${PROJECT_BINARY_DIR}/metaSMTConfig.cmake
	DESTINATION share/metaSMT)
install(EXPORT metaSMT DESTINATION share/metaSMT)

string(REPLACE ";" " " metaSMT_MLIBS "${metaSMT_LIBS}")
string(REPLACE ";" " -I" metaSMT_MINCLUDES "${metaSMT_INCLUDES}")
## create metaSMT CMake make config file
file(WRITE ${PROJECT_BINARY_DIR}/metaSMT.makefile
"metaSMT_INCLUDES := ${metaSMT_MINCLUDES}
metaSMT_LIBRARIES := ${metaSMT_MLIBS} 
")
INSTALL( FILES 
  ${PROJECT_BINARY_DIR}/metaSMT.makefile
	DESTINATION ${metaSMT_CONFIG_DIR})

## create metaSMT pkgconfig make config file
string(REPLACE ";" " " metaSMT_MLIBS "${metaSMT_LIBS}")
file(WRITE ${PROJECT_BINARY_DIR}/metaSMT.pc
"Name: metaSMT
Description: SMT Solver library
Cflags: -I${metaSMT_INCLUDES}
Libs: ${metaSMT_MLIBS} 
")
INSTALL( FILES 
  ${PROJECT_BINARY_DIR}/metaSMT.pc
	DESTINATION lib/pkgconfig/)

Feature_Summary(WHAT ALL)

# vim: ft=cmake:ts=2:sw=2:expandtab
