#define BOOST_TEST_MODULE graph_Boolector
#include <metaSMT/GraphSolver_Context.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/API/Group.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/API/Comment.hpp>


using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef GraphSolver_Context< IgnoreComments< Stack < Group< Boolector > > > > ContextType;
  ContextType ctx ;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
#include "test_Array.cpp"
#include "test_graph_copy.cpp"
#include "test_unsat.cpp"
#include "test_cardinality.cpp"
#include "test_lazy.cpp"
#include "test_group.cpp"
#include "test_stack.cpp"
#include "test_annotate.cpp"
