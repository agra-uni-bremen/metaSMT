#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/Boolector.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::Boolector> > ContextType;
#include "main.cpp"
