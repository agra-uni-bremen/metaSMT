

#include <boost/proto/debug.hpp>
#include <boost/test/unit_test.hpp>
#include <string>

#include <metaSMT/frontend/Logic.hpp>
#include <metaSMT/Group_Context.hpp>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::logic;
namespace proto = boost::proto;
using boost::dynamic_bitset;

BOOST_FIXTURE_TEST_SUITE(group_, Solver_Fixture )

BOOST_AUTO_TEST_CASE( simple_sat )
{
  BOOST_REQUIRE( solve(ctx) );
  // sat
  guard_type zero_group = current_group ( ctx ); 
  
   
  guard_type main = create_group ( ctx );
  assertion ( ctx, False ); 
  BOOST_REQUIRE ( !solve(ctx) ); 
  BOOST_REQUIRE ( !solve(ctx) ); 

  change_group ( ctx, zero_group);
  delete_group ( ctx, main ); 
  BOOST_REQUIRE ( solve(ctx) ); 

  BOOST_REQUIRE ( current_group ( ctx ) == zero_group ); 

}




BOOST_AUTO_TEST_SUITE_END() //Solver

//  vim: ft=cpp:ts=2:sw=2:expandtab
