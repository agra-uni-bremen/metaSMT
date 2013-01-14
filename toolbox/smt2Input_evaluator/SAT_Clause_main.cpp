#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/SAT_Clause.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::SAT_Clause> > ContextType;
#include "main.cpp"
