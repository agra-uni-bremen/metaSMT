add_tool_executable( sortnets_logic
  SOURCES
    logic.cpp
  REQUIRES
    Boolector_FOUND
    Z3_FOUND
    SWORD_FOUND
    CUDD_FOUND
    MiniSat_FOUND
    PicoSAT_FOUND
    Aiger_FOUND
  LIBRARIES
    ${Boost_IOSTREAMS_LIBRARY}
)

