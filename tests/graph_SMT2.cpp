#define BOOST_TEST_MODULE direct_SMT2
#define BOOST_VARIANT_VISITATION_UNROLLING_LIMIT 60
#include <metaSMT/GraphSolver_Context.hpp>
#include <metaSMT/backend/SMT2.hpp>

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
