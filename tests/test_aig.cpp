
#define BOOST_TEST_MODULE test_aig
#include <boost/test/unit_test.hpp>

//internal includes
#include <metaSMT/frontend/Logic.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/SAT_Aiger.hpp>

//external includes
#include <boost/array.hpp>
#include <boost/proto/debug.hpp>
#include <boost/proto/fusion.hpp>
#include <boost/fusion/include/io.hpp>
#include <boost/foreach.hpp>

#include <iostream>

using namespace metaSMT;

struct clause_printer
{
  void clause ( std::vector < SAT::tag::lit_tag > const& clause )
  {
    BOOST_FOREACH ( SAT::tag::lit_tag const& lit, clause )
      std::cout << lit.id << " ";
    std::cout << std::endl;
  }

  void assertion ( SAT::tag::lit_tag const& lit ) 
  { 
    std::cout << "Assertion: " << lit.id << std::endl;
  }
  void assumption ( SAT::tag::lit_tag const& lit ) 
  { 
    std::cout << "Assumption: " << lit.id << std::endl;
  }

  bool solve () 
  {
    return false; 
  }

};


class aig_Fixture {
  public:
  protected:
    DirectSolver_Context < SAT_Aiger < clause_printer > > ctx; 
};

using boost::proto::display_expr;


BOOST_FIXTURE_TEST_SUITE(aig_t, aig_Fixture )

BOOST_AUTO_TEST_CASE( syntax )
{
  using namespace logic;
  BOOST_REQUIRE_EQUAL( evaluate (ctx, False ), aiger_false);
  BOOST_REQUIRE_EQUAL( evaluate (ctx, True ), aiger_true);

  BOOST_REQUIRE_EQUAL( evaluate (ctx, Not(True) ), aiger_false);
  BOOST_REQUIRE_EQUAL( evaluate (ctx, Not(False) ), aiger_true);

  BOOST_REQUIRE_EQUAL( evaluate (ctx, Not(Not(True) )), aiger_true);
  BOOST_REQUIRE_EQUAL( evaluate (ctx, Not(Not(False)) ), aiger_false);

  predicate x = new_variable (); 
  predicate y = new_variable (); 
  assertion ( ctx, And ( x, y) ); 

  bool r = solve ( ctx ); 


    
//    BOOST_REQUIRE_EQUAL(to_aiger( True, aig )()(),aiger_true);
// 
//   display_expr( Not(False));
//   BOOST_REQUIRE_EQUAL(to_aiger ( Not(False), aig)( )(), aiger_true);
//   BOOST_REQUIRE_EQUAL(to_aiger ( Not(True ), aig)(), aiger_false);
// 
//   BOOST_REQUIRE_EQUAL(to_aiger( Not(Not(False)), aig )(), aiger_false);
//   BOOST_REQUIRE_EQUAL(to_aiger( Not(Not(True)), aig )(), aiger_true);
}

BOOST_AUTO_TEST_SUITE_END() //QF_BV

//  vim: ft=cpp:ts=2:sw=2:expandtab
