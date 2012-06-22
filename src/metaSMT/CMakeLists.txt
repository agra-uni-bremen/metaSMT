install(FILES
  Debug_Context.hpp
  DirectSolver_Context.hpp
  Graph_Context.hpp
  GraphSolver_Context.hpp
  Group_Context.hpp
  result_wrapper.hpp
  BitBlast.hpp
  Features.hpp
  Stack.hpp
  Instantiate.hpp
  DESTINATION include/metaSMT
)

install(FILES
  frontend/Logic.hpp
  frontend/QF_BV.hpp
  frontend/Array.hpp
  DESTINATION include/metaSMT/frontend
)

install(FILES
  impl/_var_id.hpp
  DESTINATION include/metaSMT/impl
)

install(FILES
  backend/Boolector.hpp
  backend/CUDD_Context.hpp
  backend/mathsat_Context.hpp
  backend/SWORD_Backend.hpp
  backend/Z3_Context.hpp
  backend/MiniSAT.hpp
  backend/PicoSAT.hpp
  backend/SAT_Aiger.hpp
  backend/Aiger.hpp
  backend/ClauseWriter.hpp
  backend/SAT_Clause.hpp
  DESTINATION include/metaSMT/backend
)

install(FILES
  support/SMT_Tag_Mapping.hpp
  DESTINATION include/metaSMT/support
)

install(FILES
  backend/SAT/model_parser.hpp
  DESTINATION include/metaSMT/backend/SAT
)

add_subdirectory(tags)
add_subdirectory(support)

# vim: ft=cmake:ts=2:sw=2:expandtab
