#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/SMT2.hpp>
#include "options.hpp"
typedef metaSMT::DirectSolver_Context< metaSMT::solver::SMT2 > ContextType;
OptionMap options;
#include "main.cpp"
