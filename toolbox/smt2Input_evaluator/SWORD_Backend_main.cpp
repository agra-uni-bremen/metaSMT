#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/SWORD_Backend.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::SWORD_Backend> > Context;
#include "main.cpp"
