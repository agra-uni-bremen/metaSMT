#define BOOST_TEST_MODULE direct_mathsat
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/mathsat_Context.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  DirectSolver_Context< mathsat_Context > ctx ;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
#include "test_Array.cpp"
#include "test_unsat.cpp"
