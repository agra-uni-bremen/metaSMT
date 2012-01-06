#include <boost/proto/debug.hpp>
#include <boost/test/unit_test.hpp>
#include <string>

#include <metaSMT/frontend/Logic.hpp>
#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/frontend/QF_UF.hpp>
#include <metaSMT/API/SymbolTable.hpp>

#include <metaSMT/expression/expression.hpp>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::logic;
using namespace metaSMT::logic::QF_BV;
using namespace metaSMT::logic::QF_UF;
using namespace metaSMT::expression;
namespace proto = boost::proto;
using boost::dynamic_bitset;

BOOST_FIXTURE_TEST_SUITE(expression_t, Solver_Fixture )

BOOST_AUTO_TEST_CASE( expression_equality ) {
  logic_expression b0 = bit0_const();
  logic_expression b1 = bit1_const();
  BOOST_REQUIRE( b0 == b0 );
  BOOST_REQUIRE( !(b0 == b1) );
  BOOST_REQUIRE( b1 == b1 );
  BOOST_REQUIRE( !(b1 == b0) );

  logic_expression p = new_variable();
  BOOST_REQUIRE( p == p );

  logic_expression q = new_variable();
  BOOST_REQUIRE( !(p == q) );
  BOOST_REQUIRE( !(q == p) );

  logic_expression bv_a = new_bitvector();
  BOOST_REQUIRE( bv_a == bv_a );
  BOOST_REQUIRE( !(p == bv_a) );

  logic_expression bv_b = new_bitvector();
  BOOST_REQUIRE( !(bv_a == bv_b) );
  BOOST_REQUIRE( !(bv_b == bv_a) );

  logic_expression and1_expr = evaluate(ctx, And(p, q));
  logic_expression and2_expr = evaluate(ctx, And(p, q));
  BOOST_REQUIRE( and1_expr == and2_expr );

  logic_expression func1 = declare_function(Boolean())(BitVector(8));
  logic_expression func2 = declare_function(Boolean())(BitVector(6));
  BOOST_REQUIRE( func1 == func1 );
  BOOST_REQUIRE( !(func1 == func2) );
}

BOOST_AUTO_TEST_SUITE_END() //Solver

//  vim: ft=cpp:ts=2:sw=2:expandtab
