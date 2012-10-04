#define BOOST_TEST_MODULE direct_Boolector
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/API/Comment.hpp>
#include <metaSMT/API/SymbolTable.hpp>
#include <metaSMT/API/Group.hpp>
#include <metaSMT/API/AssignRandomBits.hpp>
#include <metaSMT/Instantiate.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef DirectSolver_Context< AssignRandomBits< IgnoreSymbolTable< IgnoreComments< Group < Stack < Boolector > > > > > > ContextType;
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
#include "test_optimization.cpp"
#include "test_lazy.cpp"
#include "test_annotate.cpp"
#include "test_Types.cpp"
#include "test_random_bits.cpp"
#include "test_simplify.cpp"
#include "test_evaluator.cpp"
