#include <metaSMT/frontend/Array.hpp>
#include <metaSMT/frontend/QF_BV.hpp>
#include <boost/test/unit_test.hpp>
#include <boost/dynamic_bitset.hpp>
#include <string>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::logic;
using namespace metaSMT::logic::Array;
using namespace metaSMT::logic::QF_BV;
namespace proto = boost::proto;
using boost::dynamic_bitset;


BOOST_FIXTURE_TEST_SUITE(Array, Solver_Fixture )

BOOST_AUTO_TEST_CASE( variable_equality )
{
  unsigned const elem_width = 8;
  unsigned const index_width = 4;

  array x = new_array(elem_width, index_width);
  array y = new_array(elem_width, index_width);

  bool cmp = (x == x);
  BOOST_CHECK( cmp );

  cmp = (x == y);
  BOOST_CHECK( !cmp );

  cmp = (y == x);
  BOOST_CHECK( !cmp );
}

BOOST_AUTO_TEST_CASE( array_equal_t ) {
  unsigned const elem_width = 8;
  unsigned const index_width = 4;

  array a = new_array(elem_width, index_width);
  array b = new_array(elem_width, index_width);

  assumption( ctx, equal(a, b) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, nequal(a, b) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(a, b) );
  assumption( ctx, nequal(a, b) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( store_t ) {
  unsigned const elem_width = 8;
  unsigned const index_width = 4;

  array a = new_array(elem_width, index_width);
  array b = new_array(elem_width, index_width);

  // element
  bitvector e = new_bitvector(elem_width);

  // indices
  bitvector i = new_bitvector(index_width);
  bitvector j = new_bitvector(index_width);

  assumption( ctx, equal(store(a, i, e), store(a, i, e)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(a, b) );
  assumption( ctx, equal(store(a, i, e), store(b, i, e)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(a, b) );
  assumption( ctx, nequal(store(a, i, e), store(b, i, e)) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, equal(i, j) );
  assumption( ctx, equal(store(a, i, e), store(a, j, e)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(i, j) );
  assumption( ctx, nequal(store(a, i, e), store(a, j, e)) );
  BOOST_REQUIRE( !solve(ctx) );  
}

BOOST_AUTO_TEST_CASE( select_t ) {
  unsigned const elem_width = 8;
  unsigned const index_width = 4;

  array a = new_array(elem_width, index_width);
  array b = new_array(elem_width, index_width);

  // element
  bitvector e = new_bitvector(elem_width);

  // indices
  bitvector i = new_bitvector(index_width);
  bitvector j = new_bitvector(index_width);

  assumption( ctx, equal(select(a, i), select(a, i)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(a, b) );
  assumption( ctx, equal(select(a, i), select(b, i)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(a, b) );
  assumption( ctx, nequal(select(a, i), select(b, i)) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, nequal(a, b) );
  assumption( ctx, nequal(select(a, i), select(b, i)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(i, j) );
  assumption( ctx, equal(select(a, i), select(a, j)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(i, j) );
  assumption( ctx, nequal(select(a, i), select(a, j)) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( read_write_consistency ) {
  unsigned const elem_width = 8;
  unsigned const index_width = 4;

  array a = new_array(elem_width, index_width);

  // element
  bitvector e = new_bitvector(elem_width);

  // indices
  bitvector i = new_bitvector(index_width);
  bitvector j = new_bitvector(index_width);

  assumption( ctx, equal(i, j) );
  assumption( ctx, equal(select(store(a, i, e), j), e) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(i, j) );
  assumption( ctx, nequal(select(store(a, i, e), j), e) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, nequal(i, j) );
  assumption( ctx, equal( select(store(a, i, e), j), select(a, j) ) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, nequal(i, j) );
  assumption( ctx, nequal( select(store(a, i, e), j), select(a, j) ) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( read_value_from_select ) {
  unsigned const elem_width = 8;
  unsigned const index_width = 4;

  array a = new_array(elem_width, index_width);

  // initialize array: a[i] == i for all i
  unsigned const size = 1 << index_width - 1;
  for ( unsigned u = 0; u < size; ++u ) {
    assertion( ctx, equal(bvuint(u, elem_width), select(a, bvuint(u, index_width))) );
  }

  BOOST_REQUIRE( solve(ctx) );

  // check values
  for ( unsigned u = 0; u < size; ++u ) {
    ContextType::result_type expr =
      evaluate( ctx, select(a, bvuint(u, index_width)) );
    unsigned char vd = read_value( ctx, expr );
    BOOST_CHECK_EQUAL(vd, u);
  }
}

BOOST_AUTO_TEST_CASE( read_value_X ) {
  unsigned const elem_width = 8;
  unsigned const index_width = 4;
  unsigned const init_value = 42;

  array a = new_array(elem_width, index_width);
  array b = new_array(elem_width, index_width);

  // index
  bitvector i = new_bitvector(index_width);

  // element
  bitvector e = new_bitvector(elem_width);

  assertion( ctx, equal(e, bvuint(init_value, elem_width)) );
  assertion( ctx, equal(b, store(a, i, e)) );
  BOOST_REQUIRE( solve(ctx) );
  
  // uninitialized read from a[i]
  ContextType::result_type expr = evaluate(ctx, select(a, i));
  try {
    read_value( ctx, expr ).throw_if_X();
    BOOST_FAIL("unreachable");
  }
  catch(...) {
    // std::cerr << "Catched" << '\n';
  }

  // read from b[i] = e
  expr = evaluate(ctx, select(b, i));
  std::string ed = read_value( ctx, e );
  // std::cerr << ed << '\n';
  std::string vd = read_value( ctx, expr );
  // std::cerr << vd << '\n';
  BOOST_REQUIRE_EQUAL(ed, vd);
}

BOOST_AUTO_TEST_CASE( uninitialized_select ) {
  unsigned const elem_width = 32;
  unsigned const index_width = 4;

  // uninitialized array
  array a;

  // element
  bitvector e = new_bitvector(elem_width);

  // index
  bitvector i = new_bitvector(index_width);
  assertion( ctx, equal(i, bvuint(0, index_width)) ); 

  BOOST_CHECK_THROW(
    assertion(ctx, equal(e, select(a, i)))
  , std::exception
  );
}

BOOST_AUTO_TEST_SUITE_END() //Array



//  vim: ft=cpp:ts=2:sw=2:expandtab
