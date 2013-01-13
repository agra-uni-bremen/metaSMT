#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/MiniSAT.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::MiniSAT> > Context;
#include "main.cpp"
