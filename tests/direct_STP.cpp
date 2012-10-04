#define BOOST_TEST_MODULE direct_STP
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/STP.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef DirectSolver_Context< STP > ContextType;
  ContextType ctx ;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
#include "test_cardinality.cpp"
#include "test_evaluator.cpp"
