#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/SymbolTable.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>
#include "options.hpp"
typedef metaSMT::DirectSolver_Context<
  metaSMT::IgnoreSymbolTable<
    metaSMT::solver::Z3_Backend
  >
> ContextType;
OptionMap options;
#include "main.cpp"
