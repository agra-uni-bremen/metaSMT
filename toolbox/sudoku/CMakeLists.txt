add_tool_executable( sudoku 
  SOURCES 
    sudoku.cpp
  REQUIRES 
    Boolector_FOUND
    PicoSAT_FOUND
    MiniSat_FOUND
    Aiger_FOUND
    CUDD_FOUND
)

