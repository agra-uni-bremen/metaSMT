#define BOOST_TEST_MODULE graph_BitBlast_CUDD
#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/GraphSolver_Context.hpp>
#include <metaSMT/backend/CUDD_Context.hpp>
#include <metaSMT/BitBlast.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef GraphSolver_Context< BitBlast<CUDD_Context > > 
    ContextType;
  ContextType ctx;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
// #include "test_Array.cpp"
#include "test_graph_copy.cpp"
#include "test_unsat.cpp"
#include "test_lazy.cpp"
