#include <boost/test/unit_test.hpp>
#include <string>

#include <metaSMT/support/why_unsat.hpp>
#include <metaSMT/frontend/Logic.hpp>

#include <boost/assign/list_of.hpp>
#include <boost/fusion/adapted/boost_tuple.hpp>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::logic;
namespace proto = boost::proto;
using boost::dynamic_bitset;

BOOST_FIXTURE_TEST_SUITE(unsat, Solver_Fixture )

BOOST_AUTO_TEST_CASE( why_unsat1 )
{
  BOOST_REQUIRE( solve(ctx) );

  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();
  
  vector<bool> result =
    why_unsat(ctx, boost::make_tuple( Xor(d,c), b, equal(b,c), d, Not(c) ) );

  print_why_unsat(ctx, boost::make_tuple( Xor(d,c), b, equal(b,c), d, Not(c) ) );
  
  vector<bool> expected = 
    boost::assign::list_of(false)(true)(true)(false)(true);
  BOOST_REQUIRE_EQUAL_COLLECTIONS( result.begin(), result.end(), expected.begin(), expected.end());
}



BOOST_AUTO_TEST_SUITE_END() //Solver

//  vim: ft=cpp:ts=2:sw=2:expandtab
