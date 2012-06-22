#define BOOST_TEST_MODULE graph_CUDD
#include <metaSMT/GraphSolver_Context.hpp>
#include <metaSMT/backend/CUDD_Context.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef GraphSolver_Context<CUDD_Context> ContextType;
  ContextType ctx;
};

#include "test_solver.cpp"
//#include "test_QF_BV.cpp"
//#include "test_Array.hpp"
#include "test_graph_copy.cpp"
#include "test_unsat.cpp"
#include "test_lazy.cpp"
