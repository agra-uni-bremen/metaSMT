#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/ClauseWriter.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::ClauseWriter> > ContextType;
#include "main.cpp"
