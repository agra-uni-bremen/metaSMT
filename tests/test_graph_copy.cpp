#include <boost/test/unit_test.hpp>
#include <string>

#include <metaSMT/frontend/Logic.hpp>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::logic;

BOOST_FIXTURE_TEST_SUITE(test_graph_copy, Solver_Fixture )

BOOST_AUTO_TEST_CASE( copy_false )
{
  BOOST_REQUIRE( solve(ctx) );

  assertion( ctx, False );

  ContextType ctx2(ctx);
  
  BOOST_REQUIRE( !solve(ctx) );
  BOOST_REQUIRE( !solve(ctx2) );
}

BOOST_AUTO_TEST_CASE( copy_independent )
{
  BOOST_REQUIRE( solve(ctx) );

  ContextType ctx2(ctx);

  assertion( ctx, False );

  BOOST_REQUIRE( !solve(ctx) );
  BOOST_REQUIRE( solve(ctx2) );
}

BOOST_AUTO_TEST_CASE( assume_after_copy )
{
  BOOST_REQUIRE( solve(ctx) );

  ContextType ctx2(ctx);

  assumption( ctx, False );
  assumption( ctx2, True );

  BOOST_REQUIRE( !solve(ctx) );
  BOOST_REQUIRE( solve(ctx2) );
}

BOOST_AUTO_TEST_CASE( copy_assume )
{
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, False );

  ContextType ctx2(ctx);

  BOOST_REQUIRE( !solve(ctx) );
  BOOST_REQUIRE( !solve(ctx2) );

  BOOST_REQUIRE( solve(ctx) );
  BOOST_REQUIRE( solve(ctx2) );
}

BOOST_AUTO_TEST_SUITE_END() //Solver

//  vim: ft=cpp:ts=2:sw=2:expandtab
