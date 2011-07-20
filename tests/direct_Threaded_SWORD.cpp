#define BOOST_TEST_MODULE direct_Threaded_SWORD
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/UnpackFuture_Context.hpp>
#include <metaSMT/Threaded_Context.hpp>
#include <metaSMT/backend/SWORD_Backend.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/API/Comment.hpp>
#include <metaSMT/API/Group.hpp>
#include <metaSMT/Instantiate.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef DirectSolver_Context<  UnpackFuture_Context< Stack< SWORD_Backend > >  > ContextType1;
  typedef Threaded_Context< ContextType1, ContextType1 > ContextType;
  ContextType ctx ;
};

namespace std {
  //std::ostream & operator<< (std::ostream & o, Solver_Fixture::ContextType::result_type const & r) {
  //  return (o << "(Threaded result_type " << &r << ")");
  //}
  template <typename T>
  std::ostream & operator<< (std::ostream & o, boost::shared_future<T> const & f) {
    return (o << "(shared_future@" << &f << ")");
  }
} /* std */

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
//#include "test_Array.cpp"
//#include "test_group.cpp" 
#include "test_stack.cpp" 
#include "test_unsat.cpp"
#include "test_fmi.cpp"
//#include "test_cardinality.cpp"
#include "test_lazy.cpp"
//#include "test_annotate.cpp"
