#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/Aiger.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::Aiger> > ContextType;
#include "main.cpp"
