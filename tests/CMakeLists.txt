include(CMakeParseArguments)

include_directories(../src ${metaSMT_INCLUDES})

add_library(boost_test boost_test.cpp)
link_libraries(boost_test metaSMT)

find_program(AWK awk)

function (add_all_tests prog cfile)
  cmake_parse_arguments(opts "" "" "ENVIRONMENT;ARGS;" ${ARGN})
  execute_process( COMMAND
    ${AWK} -f search_tests.awk ${cfile}
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    OUTPUT_VARIABLE test_cases
  )

  string(REPLACE "\n" ";" test_cases "${test_cases}")

  foreach(test  ${test_cases})
    #message(STATUS "${prog}/${test} ${prog} -t ${test}")
    add_test("${prog}/${test}" ${prog} -t ${test} ${opts_ARGS})
    set_tests_properties ("${prog}/${test}" PROPERTIES TIMEOUT ${TIMEOUT})
    if(opts_ENVIRONMENT)
      set_tests_properties("${prog}/${test}" PROPERTIES ENVIRONMENT ${opts_ENVIRONMENT})
    endif()
  endforeach(test)
endfunction(add_all_tests)

function (add_test_executable name source )
  cmake_parse_arguments(req "" "" "REQUIRES;PROPERTIES;ARGS;LIBRARIES;ENVIRONMENT" ${ARGN})

  set(req_all 1)

  foreach( req ${req_REQUIRES} )
    if(NOT ${req} )
      set(req_all 0)
      # message("UNSATISFIED DEPENDENCY: " ${req} " of " ${name})
    endif(NOT ${req} )
  endforeach( req )

  if(req_all)
    add_executable(${name} ${source})
    add_all_tests(${name} ${source} ARGS ${req_ARGS} ENVIRONMENT ${req_ENVIRONMENT})
    if(req_LIBRARIES)
      target_link_libraries(${name} metaSMT ${req_LIBRARIES})
    endif()
    if(req_PROPERTIES)
      set_target_properties(${name} PROPERTIES ${req_PROPERTIES})
    endif()
  endif(req_all)
endfunction(add_test_executable)

add_test_executable( result_wrapper test_result_wrapper.cpp)
add_test_executable( graph test_graph.cpp)

add_test_executable( direct_SWORD direct_SWORD2.cpp REQUIRES SWORD_FOUND )
add_test_executable( graph_SWORD graph_SWORD2.cpp REQUIRES SWORD_FOUND )

find_library(PTHREAD pthread)

add_test_executable( direct_Threaded_SWORD direct_Threaded_SWORD.cpp 
  REQUIRES SWORD_FOUND Boost_THREAD_FOUND Boost_SYSTEM_FOUND
  LIBRARIES ${Boost_THREAD_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${PTHREAD}
)
add_test_executable( direct_Priority_Boolector_CUDD direct_Priority_Boolector_CUDD.cpp 
  REQUIRES Boolector_FOUND CUDD_FOUND Boost_THREAD_FOUND Boost_SYSTEM_FOUND
  LIBRARIES ${Boost_THREAD_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${PTHREAD}
)

add_test_executable( direct_CUDD direct_CUDD.cpp REQUIRES CUDD_FOUND )
add_test_executable( graph_CUDD graph_CUDD.cpp REQUIRES CUDD_FOUND )
add_test_executable( direct_BitBlast_CUDD direct_BitBlast_CUDD.cpp
  REQUIRES CUDD_FOUND)
add_test_executable( graph_BitBlast_CUDD graph_BitBlast_CUDD.cpp
  REQUIRES CUDD_FOUND)
add_test_executable(direct_CUDD_Distributed direct_CUDD_Distributed.cpp 
  REQUIRES CUDD_FOUND)

add_test_executable( direct_Boolector direct_Boolector.cpp
  REQUIRES Boolector_FOUND )
add_test_executable( graph_Boolector graph_Boolector.cpp
  REQUIRES Boolector_FOUND )
add_test_executable( SMT2Parser SMT2Parser.cpp
  REQUIRES Z3_FOUND
  LIBRARIES ${Boost_IOSTREAMS_LIBRARY} 
  )

add_test_executable( direct_Z3 direct_Z3.cpp REQUIRES Z3_FOUND )
add_test_executable( graph_Z3 graph_Z3.cpp REQUIRES Z3_FOUND )

add_test_executable( direct_STP direct_STP.cpp REQUIRES STP_FOUND )
add_test_executable( graph_STP graph_STP.cpp REQUIRES STP_FOUND )

add_test_executable( direct_MiniSAT direct_MiniSAT.cpp
  REQUIRES MiniSat_FOUND
  PROPERTIES COMPILE_FLAGS "${MiniSat_CXXFLAGS}"
  )
add_test_executable( graph_MiniSAT graph_MiniSAT.cpp
  REQUIRES MiniSat_FOUND
  PROPERTIES COMPILE_FLAGS "${MiniSat_CXXFLAGS}"
  )

add_test_executable( direct_PicoSAT direct_PicoSAT.cpp
  REQUIRES picosat_FOUND )
#add_test_executable( graph_PicoSAT graph_PicoSAT.cpp
#  REQUIRES picosat_FOUND )

add_test_executable( direct_Aiger_MiniSAT direct_Aiger_MiniSAT.cpp
  REQUIRES MiniSat_FOUND Aiger_FOUND
  PROPERTIES COMPILE_FLAGS "${MiniSat_CXXFLAGS}"
  )
add_test_executable( graph_Aiger_MiniSAT graph_Aiger_MiniSAT.cpp
  REQUIRES MiniSat_FOUND Aiger_FOUND
  PROPERTIES COMPILE_FLAGS "${MiniSat_CXXFLAGS}"
  )

add_test_executable( direct_Aiger_PicoSAT direct_Aiger_PicoSAT.cpp
  REQUIRES PicoSAT_FOUND Aiger_FOUND )
#add_test_executable( graph_Aiger_PicoSAT graph_Aiger_PicoSAT.cpp
#  REQUIRES PicoSAT_FOUND Aiger_FOUND )

if(metaSMT_USE_CW)
  find_program(PicoSAT_EXECUTABLE picosat)
  add_test_executable( direct_CW_PicoSAT direct_CW_PicoSAT.cpp
    REQUIRES PicoSAT_EXECUTABLE
    ARGS "-s no"
    ENVIRONMENT "PicoSAT_EXECUTABLE=${PicoSAT_EXECUTABLE}"
  )

  find_program(MiniSat_EXECUTABLE minisat)
  add_test_executable( direct_CW_MiniSat direct_CW_MiniSat.cpp
    REQUIRES MiniSat_EXECUTABLE
    ARGS "-s no"
    ENVIRONMENT "MiniSat_EXECUTABLE=${MiniSat_EXECUTABLE}"
  )

  find_program(PrecoSat_EXECUTABLE precosat)
  add_test_executable( direct_CW_PrecoSat direct_CW_PrecoSat.cpp
    REQUIRES Precosat_EXECUTABLE
    ARGS "-s no"
    ENVIRONMENT "PrecoSat_EXECUTABLE=${PrecoSat_EXECUTABLE}"
  )

  find_program(Plingeling_EXECUTABLE plingeling)
  add_test_executable( direct_CW_Plingeling direct_CW_Plingeling.cpp
    REQUIRES Plingeling_EXECUTABLE
    ARGS "-s no"
    ENVIRONMENT "Plingeling_EXECUTABLE=${Plingeling_EXECUTABLE}"
  )

  find_program(Glucoser_EXECUTABLE glucoser)
  add_test_executable( direct_CW_Glucoser direct_CW_Glucoser.cpp
    REQUIRES Glucoser_EXECUTABLE
    ARGS "-s no"
    ENVIRONMENT "GLUCOSER_EXECUTABLE=${Glocoser_EXECUTABLE}"
  )
endif(metaSMT_USE_CW)

if(metaSMT_USE_SMT2)
  find_program(Z3_EXECUTABLE z3)


  if (Z3_EXECUTABLE)
    execute_process(
      COMMAND echo "(check-sat) "
      COMMAND ${Z3_EXECUTABLE} -smt2 -in
      OUTPUT_VARIABLE _Z3_OUTPUT
      )
    if( _Z3_OUTPUT STREQUAL "sat\n")
      set( Z3_IS_INTERACTIVE 1)
    else()
      set( Z3_IS_INTERACTIVE 0)
    endif()
  endif()

  add_test_executable( direct_SMT2 direct_SMT2.cpp
    ARGS "--log_level=nothing"
    REQUIRES Z3_EXECUTABLE Z3_IS_INTERACTIVE
    LIBRARIES ${Boost_IOSTREAMS_LIBRARY}
    ENVIRONMENT "Z3_EXECUTABLE=${Z3_EXECUTABLE}"
  )
  add_test_executable( graph_SMT2 graph_SMT2.cpp
    ARGS "--log_level=nothing"
    REQUIRES Z3_EXECUTABLE Z3_IS_INTERACTIVE
    LIBRARIES ${Boost_IOSTREAMS_LIBRARY}
    ENVIRONMENT "Z3_EXECUTABLE=${Z3_EXECUTABLE}"
  )
endif(metaSMT_USE_SMT2)

if(metaSMT_USE_ExprSolver)
  add_test_executable( direct_ExprSolver_Boolector direct_ExprSolver_Boolector.cpp
    REQUIRES Boolector_FOUND
    LIBRARIES ${Boost_IOSTREAMS_LIBRARY})
  add_test_executable( direct_ExprSolver_Z3 direct_ExprSolver_Z3.cpp
    REQUIRES Z3_FOUND
    LIBRARIES ${Boost_IOSTREAMS_LIBRARY})
  add_test_executable( direct_ExprSolver_SMT2 direct_ExprSolver_SMT2.cpp
    ARGS "--log_level=nothing"
    REQUIRES Z3_EXECUTABLE Z3_IS_INTERACTIVE
    LIBRARIES ${Boost_IOSTREAMS_LIBRARY}
    ENVIRONMENT "Z3_EXECUTABLE=${Z3_EXECUTABLE}"
  )
endif(metaSMT_USE_ExprSolver)
# vim: ts=2 sw=2 et
