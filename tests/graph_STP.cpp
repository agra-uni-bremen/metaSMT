#define BOOST_TEST_MODULE graph_STP
#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/GraphSolver_Context.hpp>
#include <metaSMT/backend/STP.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef GraphSolver_Context< STP > ContextType;
  ContextType ctx ;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
#include "test_graph_copy.cpp"
#include "test_cardinality.cpp"
#include "test_evaluator.cpp"
