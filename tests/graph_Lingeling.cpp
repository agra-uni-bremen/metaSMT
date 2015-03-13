#define BOOST_TEST_MODULE graph_Lingeling
#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/GraphSolver_Context.hpp>
#include <metaSMT/backend/SAT_Clause.hpp>
#include <metaSMT/backend/Lingeling.hpp>
#include <metaSMT/BitBlast.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture
{
  typedef GraphSolver_Context< BitBlast < SAT_Clause < Lingeling > > > ContextType;
  ContextType ctx ;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
// #include "test_Array.cpp"
// #include "test_group.cpp"
#include "test_unsat.cpp"
#include "test_lazy.cpp"
#include "test_evaluator.cpp"
