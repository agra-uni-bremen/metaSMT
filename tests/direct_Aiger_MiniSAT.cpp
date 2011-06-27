
#define BOOST_TEST_MODULE direct_MiniSAT
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/SAT_Aiger.hpp>
#include <metaSMT/backend/MiniSAT.hpp>
#include <metaSMT/API/Group.hpp>
#include <metaSMT/BitBlast.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture
{
  typedef DirectSolver_Context<  Group< BitBlast < SAT_Aiger < MiniSAT > > > > ContextType;
  ContextType ctx ;
};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
// #include "test_Array.cpp"
#include "test_group.cpp"
#include "test_unsat.cpp"
#include "test_lazy.cpp"
