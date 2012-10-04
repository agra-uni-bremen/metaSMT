#define BOOST_TEST_MODULE direct_SMT2
#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/GraphSolver_Context.hpp>
#include <metaSMT/backend/SMT2.hpp>
#include <metaSMT/API/Stack.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture
{
  typedef GraphSolver_Context< SMT2 > ContextType;
  ContextType ctx ;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
#include "test_annotate.cpp"
// #include "test_Array.cpp"
//#include "test_group.cpp"
//#include "test_unsat.cpp"
//#include "test_lazy.cpp"
#include "test_cardinality.cpp"
#include "test_evaluator.cpp"
