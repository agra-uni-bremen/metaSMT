add_tool_executable( smt2InputEvaluator_Boolector
  SOURCES
    Boolector_main.cpp
  REQUIRES
    Boolector_FOUND
)

add_tool_executable( smt2InputEvaluator_ClauseWriter
  SOURCES
    ClauseWriter_main.cpp
  REQUIRES
    ClauseWriter_FOUND
)

add_tool_executable( smt2InputEvaluator_CUDD_Context
  SOURCES
    CUDD_Context_main.cpp
  REQUIRES
    CUDD_Context_FOUND
)

add_tool_executable( smt2InputEvaluator_CUDD_Distributed
  SOURCES
    CUDD_Distributed_main.cpp
  REQUIRES
    CUDD_Distributed_FOUND
)

add_tool_executable( smt2InputEvaluator_ExpressionSolver
  SOURCES
    ExpressionSolver_main.cpp
  REQUIRES
    ExpressionSolver_FOUND
)

add_tool_executable( smt2InputEvaluator_MiniSAT
  SOURCES
    MiniSAT_main.cpp
  REQUIRES
    MiniSAT_FOUND
)

#add_tool_executable( smt2InputEvaluator_PicoSAT
#  SOURCES
#    PicoSAT_main.cpp
#  REQUIRES
#    PicoSAT_FOUND
#)

add_tool_executable( smt2InputEvaluator_SAT_Aiger
  SOURCES
    SAT_Aiger_main.cpp
  REQUIRES
    SAT_Aiger_FOUND
)

add_tool_executable( smt2InputEvaluator_SAT_Clause
  SOURCES
    SAT_Clause_main.cpp
  REQUIRES
    SAT_Clause_FOUND
)

add_tool_executable( smt2InputEvaluator_SMT2
  SOURCES
    SMT2_main.cpp
  REQUIRES
    SMT2_FOUND
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
