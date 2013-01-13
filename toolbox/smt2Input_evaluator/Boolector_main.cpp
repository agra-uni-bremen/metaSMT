#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/Boolector.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::Boolector> > Context;
#include "main.cpp"
