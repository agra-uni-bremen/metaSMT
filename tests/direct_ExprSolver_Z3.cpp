#define BOOST_TEST_MODULE direct_ExprSolver_Z3
#define BOOST_VARIANT_VISITATION_UNROLLING_LIMIT 60
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>
#include <metaSMT/backend/ExpressionSolver.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef DirectSolver_Context< ExpressionSolver< Z3_Backend > > ContextType;
  ContextType ctx ;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
