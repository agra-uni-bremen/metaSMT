add_tool_executable( smt2InputEvaluator_Boolector
  SOURCES
    Boolector_main.cpp
  REQUIRES
    Boolector_FOUND
)

add_tool_executable( smt2InputEvaluator_MiniSAT
  SOURCES
    MiniSAT_main.cpp
  REQUIRES
    MiniSat_FOUND
)

add_tool_executable( smt2InputEvaluator_PicoSAT
  SOURCES
    PicoSAT_main.cpp
  REQUIRES
    picosat_FOUND
)

add_tool_executable( smt2InputEvaluator_SMT2
  SOURCES
    SMT2_main.cpp
  REQUIRES
    Z3_FOUND
  LIBRARIES
    ${Boost_IOSTREAMS_LIBRARY} 
)

add_tool_executable( smt2InputEvaluator_STP
  SOURCES
    STP_main.cpp
  REQUIRES
    STP_FOUND
)

add_tool_executable( smt2InputEvaluator_SWORD_Backend
  SOURCES
    SWORD_Backend_main.cpp
  REQUIRES
    SWORD_FOUND
)

add_tool_executable( smt2InputEvaluator_Z3_Backend
  SOURCES
    Z3_Backend_main.cpp
  REQUIRES
    Z3_FOUND
)
