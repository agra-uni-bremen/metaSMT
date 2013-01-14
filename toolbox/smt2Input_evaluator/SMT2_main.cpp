#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/SMT2.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::SMT2> > ContextType;
#include "main.cpp"
