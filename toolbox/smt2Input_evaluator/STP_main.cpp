#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/STP.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::STP> > Context;
#include "main.cpp"
