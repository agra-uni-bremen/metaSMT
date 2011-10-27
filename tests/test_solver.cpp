#include <boost/proto/debug.hpp>
#include <boost/test/unit_test.hpp>
#include <string>

#include <metaSMT/frontend/Logic.hpp>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::logic;
namespace proto = boost::proto;
using boost::dynamic_bitset;

BOOST_FIXTURE_TEST_SUITE(solver, Solver_Fixture )

BOOST_AUTO_TEST_CASE( simple_unsat )
{
  // unsat
  assertion( ctx, False);
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( simple_sat )
{
  BOOST_REQUIRE( solve(ctx) );
  // sat
  assertion( ctx, True);
  BOOST_REQUIRE( solve(ctx) );

  // unsat
  assumption( ctx, False);
  BOOST_REQUIRE( !solve(ctx) );
}


BOOST_AUTO_TEST_CASE( incremental )
{
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, False);
  BOOST_REQUIRE( !solve(ctx) );
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( equal_t )
{
  predicate x = new_variable();
  predicate y = new_variable();
  // equal
  assumption( ctx, metaSMT::logic::equal(x, x));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, metaSMT::logic::equal(x, y));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, metaSMT::logic::equal(x, True));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, metaSMT::logic::equal(x, False));
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, metaSMT::logic::equal(True, True ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, metaSMT::logic::equal(False, False) );
  BOOST_REQUIRE( solve(ctx) );

  // nequal
  assumption( ctx, metaSMT::logic::equal(True, False));
  BOOST_REQUIRE( !solve(ctx) );
  assumption( ctx, metaSMT::logic::equal(False, True));
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( nequal_t)
{
  predicate x = new_variable();
  predicate y = new_variable();
  // nequal
  assumption( ctx, nequal(x, y));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, nequal(x, True));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, nequal(x, False));
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, nequal(False, True ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, nequal(True, False) );
  BOOST_REQUIRE( solve(ctx) );

  // equal
  assumption( ctx, nequal(False, False));
  BOOST_REQUIRE( !solve(ctx) );
  assumption( ctx, nequal(True, True));
  BOOST_REQUIRE( !solve(ctx) );
  assumption( ctx, nequal(x, x));
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( read_value_t)
{
  predicate x = new_variable();
  predicate y = new_variable();
  bool xb,yb;

  assumption( ctx, metaSMT::logic::equal(x, y));
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx,x);
  yb = read_value(ctx,y);
  BOOST_CHECK_EQUAL(xb,yb);

  assumption( ctx, nequal(x, y));
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx,x);
  yb = read_value(ctx,y);
  BOOST_CHECK(xb != yb);

  assumption( ctx, And(x, y));
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx,x);
  yb = read_value(ctx,y);
  BOOST_CHECK(xb && yb);

  assumption( ctx, Or(x, y));
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx,x);
  yb = read_value(ctx,y);
  BOOST_CHECK(xb || yb);
}

BOOST_AUTO_TEST_CASE( read_value_xor )
{
  predicate x = new_variable();
  predicate y = new_variable();
  bool xb,yb;

  assumption( ctx, Xor(x, y));
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx,x);
  yb = read_value(ctx,y);
  BOOST_CHECK(xb^yb);

  assumption( ctx, Xor(x, True));
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx,x);
  BOOST_CHECK_EQUAL(xb, false);

  assumption( ctx, Xor(x, False));
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx,x);
  BOOST_CHECK_EQUAL(xb, true);

  assumption( ctx, Xor(x, x));
  BOOST_CHECK( !solve(ctx) );

}

BOOST_AUTO_TEST_CASE( not_t )
{
  predicate x = new_variable();

  assumption( ctx, Not(False) );
  BOOST_CHECK( solve(ctx) );
  assumption( ctx, Not(True) );
  BOOST_CHECK( !solve(ctx) );
  assumption( ctx, Not(Not(True)) );
  BOOST_CHECK( solve(ctx) );

  assumption( ctx, metaSMT::logic::equal( x, Not(x) ) );
  BOOST_CHECK( !solve(ctx) );
  assumption( ctx, nequal( x, Not(Not(x))) );
  BOOST_CHECK( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( implies_t )
{
  predicate x = new_variable();
  bool xb;

  assumption( ctx, implies(False, False));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, implies(False, True));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, implies(True, False));
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, implies(x, False));
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx,x);
  BOOST_CHECK_EQUAL(xb, false);

  assumption( ctx, nequal(implies(True, x), x));
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, Not(implies(False, x)) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( ite_t )
{
  predicate x = new_variable();
  bool xb;

  assumption( ctx, Ite(False, False, True));
  BOOST_CHECK( solve(ctx) );
  assumption( ctx, Ite(True, True, False));
  BOOST_CHECK( solve(ctx) );
  assumption( ctx, Ite(False, True, False));
  BOOST_CHECK( !solve(ctx) );
  assumption( ctx, Ite(True, False, True));
  BOOST_CHECK( !solve(ctx) );

  assumption( ctx, implies(x, False));
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx,x);
  BOOST_CHECK_EQUAL(xb, false);

  assumption( ctx, nequal(implies(True, x), x));
  BOOST_CHECK( !solve(ctx) );

  assumption( ctx, Not(implies(False, x)) );
  BOOST_CHECK( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( or_t )
{
  predicate x = new_variable();
  predicate y = new_variable();
  bool xb,yb;

  assumption( ctx, Or(False, False));
  BOOST_CHECK( !solve(ctx) );
  assumption( ctx, Or(False, True));
  BOOST_CHECK( solve(ctx) );
  assumption( ctx, Or(True, False));
  BOOST_CHECK( solve(ctx) );
  assumption( ctx, Or(True, True));
  BOOST_CHECK( solve(ctx) );
  
  assumption( ctx, Or(x, y) );
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx,x);
  yb = read_value(ctx,y);
  BOOST_CHECK(xb|yb);
}

BOOST_AUTO_TEST_CASE( nor_t )
{
  predicate x = new_variable();
  predicate y = new_variable();
  bool xb, yb;

  assumption( ctx, Nor(False, False) );
  BOOST_CHECK( solve(ctx) );
  assumption( ctx, Nor(False, True) );
  BOOST_CHECK( !solve(ctx) );
  assumption( ctx, Nor(True, False) );
  BOOST_CHECK( !solve(ctx) );
  assumption( ctx, Nor(True, True) );
  BOOST_CHECK( !solve(ctx) );
  
  assumption( ctx, Nor(x, y) );
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx, x);
  yb = read_value(ctx, y);
  BOOST_CHECK(!(xb | yb));
}

BOOST_AUTO_TEST_CASE( and_t )
{
  predicate x = new_variable();
  predicate y = new_variable();
  bool xb,yb;

  assumption( ctx, And(False, False));
  BOOST_CHECK( !solve(ctx) );
  assumption( ctx, And(False, True));
  BOOST_CHECK( !solve(ctx) );
  assumption( ctx, And(True, False));
  BOOST_CHECK( !solve(ctx) );
  assumption( ctx, And(True, True));
  BOOST_CHECK( solve(ctx) );
  
  assumption( ctx, And(x, y));
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx, x);
  yb = read_value(ctx, y);
  BOOST_CHECK( xb & yb );
}

BOOST_AUTO_TEST_CASE( nand_t )
{
  predicate x = new_variable();
  predicate y = new_variable();
  bool xb,yb;

  assumption( ctx, Nand(False, False));
  BOOST_CHECK( solve(ctx) );
  assumption( ctx, Nand(False, True));
  BOOST_CHECK( solve(ctx) );
  assumption( ctx, Nand(True, False));
  BOOST_CHECK( solve(ctx) );
  assumption( ctx, Nand(True, True));
  BOOST_CHECK( !solve(ctx) );
  
  assumption( ctx, Nand(x, y));
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx, x);
  yb = read_value(ctx, y);
  BOOST_CHECK(!(xb & yb));
}

BOOST_AUTO_TEST_CASE( xor_t )
{
   predicate x = new_variable();
   predicate y = new_variable();
   bool xb,yb;

   assumption( ctx, Xor(False, False));
   BOOST_CHECK( !solve(ctx) );
   assumption( ctx, Xor(False, True));
   BOOST_CHECK( solve(ctx) );
   assumption( ctx, Xor(True, False));
   BOOST_CHECK( solve(ctx) );
   assumption( ctx, Xor(True, True));
   BOOST_CHECK( !solve(ctx) );
  
   assumption( ctx, Xor(x, y));
   BOOST_REQUIRE( solve(ctx) );
   xb = read_value(ctx, x);
   yb = read_value(ctx, y);
   BOOST_CHECK(xb ^ yb);
} 


BOOST_AUTO_TEST_CASE( xnor_t )
{
  predicate x = new_variable();
  predicate y = new_variable();
  bool xb,yb;

  assumption( ctx, Xnor(False, False));
  BOOST_CHECK( solve(ctx) );
  assumption( ctx, Xnor(False, True));
  BOOST_CHECK( !solve(ctx) );
  assumption( ctx, Xnor(True, False));
  BOOST_CHECK( !solve(ctx) );
  assumption( ctx, Xnor(True, True));
  BOOST_CHECK( solve(ctx) );
  
  assumption( ctx, Xnor(x, y));
  BOOST_REQUIRE( solve(ctx) );
  xb = read_value(ctx, x);
  yb = read_value(ctx, y);
  BOOST_CHECK(!(xb ^ yb));
}

BOOST_AUTO_TEST_CASE( eval_result_type ) {
  predicate x = new_variable();
  ContextType::result_type r = evaluate( ctx, metaSMT::logic::equal(x, True) );
  metaSMT::assertion( ctx, r );
}

BOOST_AUTO_TEST_CASE( read_result_type ) {
  predicate x = new_variable();
  ContextType::result_type r = evaluate( ctx, x );
  metaSMT::assertion( ctx, metaSMT::logic::equal(r, True) );
  BOOST_REQUIRE( solve(ctx) );
  bool rb = read_value(ctx, r);
  bool xb = read_value(ctx, x);
  BOOST_REQUIRE_EQUAL( xb, rb );
}

BOOST_AUTO_TEST_CASE( predicate_constant )
{
  assumption( ctx, equal(True, predicate_const(true)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, nequal(True, predicate_const(true)) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, equal(False, predicate_const(false)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, nequal(False, predicate_const(false)) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, equal(True, predicate_const(false)) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, nequal(True, predicate_const(false)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(False, predicate_const(true)) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, nequal(False, predicate_const(true)) );
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_SUITE_END() //Solver

//  vim: ft=cpp:ts=2:sw=2:expandtab
