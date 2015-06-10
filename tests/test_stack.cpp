#include <boost/proto/debug.hpp>
#include <boost/test/unit_test.hpp>
#include <string>

#include <metaSMT/frontend/Logic.hpp>
#include <metaSMT/API/Stack.hpp>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::logic;
namespace proto = boost::proto;
using boost::dynamic_bitset;

BOOST_FIXTURE_TEST_SUITE(stack_test, Solver_Fixture )

BOOST_AUTO_TEST_CASE( simple_sat )
{
  BOOST_REQUIRE( solve(ctx) );
  // sat

  push( ctx );

  assertion ( ctx, False );
  BOOST_REQUIRE ( !solve(ctx) );
  // unsat
  BOOST_REQUIRE ( !solve(ctx) );
  // still unsat

  pop( ctx );
  BOOST_REQUIRE ( solve(ctx) );
}


BOOST_AUTO_TEST_SUITE_END() //Solver

//  vim: ft=cpp:ts=2:sw=2:expandtab
