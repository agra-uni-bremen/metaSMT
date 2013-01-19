#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/backend/SWORD_Backend.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::Stack<metaSMT::solver::SWORD_Backend> > ContextType;
#include "main.cpp"
