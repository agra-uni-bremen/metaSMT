#define BOOST_TEST_MODULE direct_Priority_Boolector_CUDD
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/UnpackFuture_Context.hpp>
#include <metaSMT/Priority_Context.hpp>
#include <metaSMT/backend/CUDD_Context.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/BitBlast.hpp>

#include <metaSMT/API/Stack.hpp>
#include <metaSMT/API/Comment.hpp>
#include <metaSMT/API/Group.hpp>
#include <metaSMT/Instantiate.hpp>

using namespace metaSMT::solver;
using namespace metaSMT;
struct Solver_Fixture {
  typedef DirectSolver_Context<  UnpackFuture_Context< Stack <Boolector > >   > ContextType2;

  typedef DirectSolver_Context<  UnpackFuture_Context< Stack <BitBlast<CUDD_Context> > > > ContextType1;

  typedef Priority_Context< ContextType1, ContextType2 > ContextType;
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

BOOST_FIXTURE_TEST_SUITE(check_priority,Solver_Fixture)
BOOST_AUTO_TEST_CASE( no_smt_after_bdd )
{ 
  const unsigned limit = 256;
  unsigned prev0 = 0;
  unsigned prev1 = 0;
  bool ctx1Ready = false;
 
  BOOST_REQUIRE( solve(ctx) );

  for (unsigned i = 0; i < limit; i++) {

   unsigned current1 = ctx.get_count1();
   unsigned current0 = ctx.get_count0();
   //current0 ist BDD- und current1 ist SMT-solver
   BOOST_REQUIRE( solve(ctx) );

   if( prev0 != current0 )
   {
     ctx1Ready = true;
     BOOST_REQUIRE_EQUAL(prev1,current1);
     BOOST_REQUIRE_EQUAL(prev0+1,current0);
   } else {

     BOOST_REQUIRE(!ctx1Ready);
     BOOST_REQUIRE_EQUAL(prev0,current0);
     BOOST_REQUIRE_EQUAL(prev1+1,current1);
   }
   
   prev1 = current1;
   prev0 = current0;

  }
  BOOST_REQUIRE_GT(prev0,0u);
}

BOOST_AUTO_TEST_CASE( no_smt_after_bdd_bvmul )
{ 
  unsigned const w = 12;
  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  
  const unsigned limit = 256;
  unsigned prev0 = 0;
  unsigned prev1 = 0;
  bool ctx1Ready = false;
 
  assertion( ctx, equal( bvmul( x, y ),bvuint(1256,w) ) ); 
  BOOST_REQUIRE( solve(ctx) );

 
  for (unsigned i = 0; i < limit; i++) {

   unsigned current1 = ctx.get_count1();
   unsigned current0 = ctx.get_count0();
   //current0 ist BDD- und current1 ist SMT-solver
   BOOST_REQUIRE( solve(ctx) );

   if( prev0 != current0 )
   {
     ctx1Ready = true;
     BOOST_REQUIRE_EQUAL(prev1,current1);
     BOOST_REQUIRE_EQUAL(prev0+1,current0);
   } else {

     BOOST_REQUIRE(!ctx1Ready);
     BOOST_REQUIRE_EQUAL(prev0,current0);
     BOOST_REQUIRE_EQUAL(prev1+1,current1);
   }
   
   prev1 = current1;
   prev0 = current0;

  }
  BOOST_REQUIRE_GT(prev0,0u);
};


BOOST_AUTO_TEST_SUITE_END()
