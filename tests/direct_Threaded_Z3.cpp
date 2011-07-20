#define BOOST_TEST_MODULE direct_Threaded_Z3
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/Threaded_Context.hpp>
#include <metaSMT/backend/Z3.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/API/Comment.hpp>
#include <metaSMT/API/Group.hpp>
#include <metaSMT/Instantiate.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef DirectSolver_Context< IgnoreComments< Group < Stack < Z3 > > > > ContextType1;
  typedef Threaded_Context< ContextType1, ContextType1 > ContextType;
  ContextType ctx ;
};

#include "test_solver.cpp"
//#include "test_QF_BV.cpp"
//#include "test_Array.cpp"
//#include "test_group.cpp" 
//#include "test_stack.cpp" 
//#include "test_unsat.cpp"
//#include "test_fmi.cpp"
//#include "test_cardinality.cpp"
//#include "test_lazy.cpp"
//#include "test_annotate.cpp"
