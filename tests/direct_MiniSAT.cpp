
#define BOOST_TEST_MODULE direct_MiniSAT
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/SAT_Clause.hpp>
#include <metaSMT/backend/MiniSAT.hpp>
#include <metaSMT/API/Group.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/BitBlast.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture
{
  typedef DirectSolver_Context<  Stack< Group < BitBlast < SAT_Clause < MiniSAT > > > > > ContextType;
  ContextType ctx ;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
// #include "test_Array.cpp"
#include "test_group.cpp"
#include "test_unsat.cpp"
#include "test_cardinality.cpp"
#include "test_optimization.cpp"
#include "test_evaluator.cpp"
