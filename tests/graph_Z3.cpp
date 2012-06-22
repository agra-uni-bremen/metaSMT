#define BOOST_TEST_MODULE graph_Z3
#include <metaSMT/GraphSolver_Context.hpp>
#include <metaSMT/backend/Z3_Context.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef GraphSolver_Context< Z3_Context > ContextType;
  ContextType ctx ;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
#include "test_Array.cpp"
#include "test_graph_copy.cpp"
#include "test_cardinality.cpp"
#include "test_lazy.cpp"
#include "test_stack.cpp"
