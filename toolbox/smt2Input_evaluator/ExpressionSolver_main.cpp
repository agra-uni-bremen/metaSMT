#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/ExpressionSolver.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::ExpressionSolver> > Context;
#include "main.cpp"
