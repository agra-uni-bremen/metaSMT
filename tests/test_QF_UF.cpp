#include <metaSMT/frontend/QF_UF.hpp>
#include <metaSMT/frontend/QF_BV.hpp>
#include <boost/test/unit_test.hpp>
#include <boost/dynamic_bitset.hpp>
#include <string>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::logic;
using namespace metaSMT::logic::QF_UF;
using namespace metaSMT::logic::QF_BV;
namespace proto = boost::proto;
using boost::dynamic_bitset;


BOOST_FIXTURE_TEST_SUITE(QF_UF, Solver_Fixture )

BOOST_AUTO_TEST_CASE( equal_bool ) {
  using namespace type;

  unsigned const w = 8;
  Uninterpreted_Function f = declare_function(Boolean())(BitVector(w));
  bitvector x = new_bitvector(w);

  assertion(ctx, equal(f(x), f(x)) );
  BOOST_REQUIRE( solve(ctx) );

  assertion(ctx, nequal(f(x), f(x)) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( equal_bitvector ) {
  using namespace type;
  unsigned const result_width = 4;
  unsigned const param_width = 8;
  Uninterpreted_Function f = declare_function(BitVector(result_width))(BitVector(param_width));
  bitvector x = new_bitvector(param_width);

  assertion(ctx, equal(f(x), f(x)) );
  BOOST_REQUIRE( solve(ctx) );

  assertion(ctx, nequal(f(x), f(x)) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( functional_consistency ) {
  using namespace type;

  unsigned const w = 8;
  Uninterpreted_Function f = declare_function(Boolean())(BitVector(w));
  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);  

  // functional consistency:
  //   ( x == y ) --> ( f(x) == f(y) )
  assertion(ctx, equal(x, y) );

  assertion(ctx, equal(f(x), f(y)) );
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( two_arguments ) {
  using namespace type;
  unsigned const w = 8;

  Uninterpreted_Function f = declare_function(Boolean())(BitVector(w))(BitVector(w));
  bitvector x = new_bitvector(w);

  assertion(ctx, equal(f(x,x), f(x,x)));
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( three_arguments ) {
  using namespace type;
  unsigned const w = 8;

  Uninterpreted_Function f = declare_function(Boolean())(BitVector(w))(BitVector(w))(BitVector(w));
  bitvector x = new_bitvector(w);

  assertion(ctx, equal(f(x,x,x), f(x,x,x)));
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_SUITE_END() // QF_UF

//  vim: ft=cpp:ts=2:sw=2:expandtab
