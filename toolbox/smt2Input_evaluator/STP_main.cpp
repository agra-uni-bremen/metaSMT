#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/API/SymbolTable.hpp>
#include <metaSMT/backend/STP.hpp>
#include "options.hpp"
typedef metaSMT::DirectSolver_Context<
  metaSMT::IgnoreSymbolTable<
    metaSMT::Stack<metaSMT::solver::STP>
  >
> ContextType;
OptionMap options;
#include "main.cpp"
