#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::Z3_Backend> > ContextType;
#include "main.cpp"
