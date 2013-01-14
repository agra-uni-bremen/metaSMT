#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/SAT_Aiger.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::SAT_Aiger> > ContextType;
#include "main.cpp"
