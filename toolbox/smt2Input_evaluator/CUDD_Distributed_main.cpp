#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/CUDD_Distributed.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::CUDD_Distributed> > ContextType;
#include "main.cpp"
