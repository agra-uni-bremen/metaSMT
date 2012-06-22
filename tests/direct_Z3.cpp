#define BOOST_TEST_MODULE direct_Z3
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/Z3_Context.hpp>
#include <metaSMT/Stack.hpp>
#include <metaSMT/Group_Context.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef DirectSolver_Context< Group_Context < Z3_Context > >
    ContextType;
  ContextType ctx ;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
#include "test_Array.cpp"
#include "test_group.cpp"
#include "test_unsat.cpp"
#include "test_cardinality.cpp"
#include "test_stack.cpp"
