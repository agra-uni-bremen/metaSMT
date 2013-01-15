#define BOOST_TEST_MODULE SMT2Parser 
#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/API/Options.hpp>
#include <metaSMT/backend/SMT2.hpp>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::solver;
struct Solver_Fixture {
public:
  typedef DirectSolver_Context< SMT2 > ContextType;
  Solver_Fixture() {
    set_option(ctx, "solver_executable", "smt2InputEvaluator_Z3_Backend");
    set_option(ctx, "solver_arguments", "");
  }
  ContextType ctx;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
//#include "test_QF_UF.cpp"
//#include "test_annotate.cpp"
//#include "test_stack.cpp"
//#include "test_Array.cpp"
//#include "test_Types.cpp"
//#include "test_cardinality.cpp"
//#include "test_optimization.cpp"
//#include "test_expression.cpp"
//#include "test_simplify.cpp"
