add_tool_executable( guess_mastermind 
  SOURCES 
    guess.cpp
  REQUIRES 
    Boolector_FOUND
    CUDD_FOUND
    MiniSat_FOUND
    PicoSAT_FOUND
)

