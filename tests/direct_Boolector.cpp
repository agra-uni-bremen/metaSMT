#define BOOST_TEST_MODULE direct_Boolector
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/Stack.hpp>
#include <metaSMT/Comment.hpp>
#include <metaSMT/Group_Context.hpp>
#include <metaSMT/Instantiate.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef DirectSolver_Context< IgnoreComments< Group_Context < Stack < Boolector > > > > ContextType;
  ContextType ctx ;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
#include "test_Array.cpp"
#include "test_group.cpp" 
#include "test_stack.cpp" 
#include "test_unsat.cpp"
#include "test_fmi.cpp"
#include "test_cardinality.cpp"
#include "test_lazy.cpp"
#include "test_annotate.cpp"
