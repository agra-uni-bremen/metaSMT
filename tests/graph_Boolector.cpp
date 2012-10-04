#define BOOST_TEST_MODULE graph_Boolector
#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/GraphSolver_Context.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/API/Comment.hpp>
#include <metaSMT/API/SymbolTable.hpp>
#include <metaSMT/API/Group.hpp>


using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef GraphSolver_Context< IgnoreSymbolTable< IgnoreComments< Group < Stack < Boolector > > > > > ContextType;
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
#include "test_evaluator.cpp"
