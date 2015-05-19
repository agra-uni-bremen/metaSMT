
define_property(
  GLOBAL
  PROPERTY TOOLBOX_SORTNETS_BENCHMARKS
  BRIEF_DOCS "list of sortnet benchmarks"
  FULL_DOCS "list of sortnet benchmarks"
)


function(add_sortnet name)
  add_tool_executable( sortnets_${name}
    SOURCES
      ${name}.cpp

    REQUIRES
      ${ARGN}
  )

  add_sortnet_benchmark(sortnets_${name} 1 unsorted_6.txt)
  add_sortnet_benchmark(sortnets_${name} 5 unsorted_6.txt)
  add_sortnet_benchmark(sortnets_${name} 1 unsorted_7.txt)
  add_sortnet_benchmark(sortnets_${name} 6 unsorted_7.txt)
  add_sortnet_benchmark(sortnets_${name} 6 unsorted_8.txt)

endfunction(add_sortnet)

function(add_sortnet_benchmark target depth benchmark)
  if(TARGET ${target})
    message(STATUS "add_sortnet_benchmark ${target} ${depth} ${benchmark}")
    set(datafile "${CMAKE_CURRENT_SOURCE_DIR}/${benchmark}")
    set(logfile "${CMAKE_CURRENT_BINARY_DIR}/${target}_${depth}_${benchmark}.log")
    add_custom_command(
      OUTPUT ${logfile}
      COMMAND cat ${datafile} | ${CMAKE_COMMAND} -E time xargs $<TARGET_FILE:${target}> ${depth} &> ${logfile}
      DEPENDS ${datafile} ${target}
    )

    set_property(GLOBAL APPEND PROPERTY TOOLBOX_SORTNETS_BENCHMARKS ${logfile})
  endif()
endfunction(add_sortnet_benchmark)

add_sortnet(boolector Boolector_FOUND MiniSat_FOUND Aiger_FOUND)
add_sortnet(cvc4 CVC4_FOUND)
add_sortnet(minisat MiniSat_FOUND Aiger_FOUND)
add_sortnet(picosat PicoSAT_FOUND MiniSat_FOUND Aiger_FOUND)
add_sortnet(smt2)
add_sortnet(stp STP_FOUND)
add_sortnet(sword SWORD_FOUND)
add_sortnet(z3 Z3_FOUND)

get_property(benchmarks GLOBAL PROPERTY TOOLBOX_SORTNETS_BENCHMARKS)
add_custom_target(
  benchmark_sortnets
  ${CMAKE_COMMAND} -E echo_append
  DEPENDS ${benchmarks}
  COMMENT ""
)
