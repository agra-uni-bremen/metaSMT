#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/PicoSAT.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::PicoSAT> > Context;
#include "main.cpp"
