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

BOOST_AUTO_TEST_CASE( equal_t ) {
  unsigned const elem_width = 32;
  unsigned const index_width = 1;

  array a = new_array(elem_width, index_width);
  array b = new_array(elem_width, index_width);

  assumption( ctx, equal(a, b) );

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, nequal(a, b) );

  BOOST_REQUIRE( solve(ctx) );

  assertion( ctx, equal(a, b) );
  assertion( ctx, nequal(a, b) );

  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( equal2_t ) {
  unsigned const elem_width = 32;
  unsigned const index_width = 1;

  array a = new_array(elem_width, index_width);
  array b = new_array(elem_width, index_width);

  assertion( ctx, equal(a, b) );

  BOOST_REQUIRE( solve(ctx) );

  assertion( ctx, nequal(a, b) );

  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( store_equal ) {
  unsigned const elem_width = 32;
  unsigned const index_width = 1;

  array a = new_array(elem_width, index_width);
  array b = new_array(elem_width, index_width);

  bitvector x = new_bitvector(elem_width);
  bitvector idx = new_bitvector(index_width);

  assumption( ctx, equal(store(a, idx, x), store(a, idx, x)) );

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(a, b) );
  assumption( ctx, equal(store(a, idx, x), store(b, idx, x)) );

  BOOST_REQUIRE( solve(ctx) );


  assumption( ctx, equal(a, b) );
  assumption( ctx, nequal(store(a, idx, x), store(b, idx, x)) );

  BOOST_REQUIRE( !solve(ctx) );
}


BOOST_AUTO_TEST_CASE( read_write_value )
{
  unsigned const elem_width = 32;
  unsigned const index_width = 1;
  unsigned const init_value = 128;

  bitvector x = new_bitvector(elem_width);
  bitvector y = new_bitvector(elem_width);
  array a = new_array(elem_width, index_width);
  array b = new_array(elem_width, index_width);

  bitvector idx = new_bitvector(index_width);

  unsigned xd, yd, idxd;

  BOOST_REQUIRE( solve(ctx) );

  assertion( ctx, equal(idx, bvuint(0, index_width)) );
  assertion( ctx, equal(x, bvuint(init_value, elem_width)) );

  assertion( ctx, equal(store(a, idx, x), b) );
  assertion( ctx, equal(y, select(b, idx) ) );

  BOOST_REQUIRE( solve(ctx) );

  idxd = read_value(ctx, idx);
  xd = read_value(ctx, x);
  std::cout << read_value(ctx, x) << std::endl;
  yd = read_value(ctx, y);
  std::cout << read_value(ctx, y) << std::endl;

  BOOST_CHECK_EQUAL(idxd, 0u);
  BOOST_CHECK_EQUAL(xd, init_value);
  BOOST_CHECK_EQUAL(yd, init_value);
  BOOST_CHECK_EQUAL(xd, yd);
}

BOOST_AUTO_TEST_CASE( read_write_value2 )
{
  unsigned const elem_width = 32;
  unsigned const index_width = 1;

  bitvector x = new_bitvector(elem_width);
  array a = new_array(elem_width, index_width);

  bitvector idx = new_bitvector(index_width);

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( select(store(a, idx, x), idx), x) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, nequal( select(store(a, idx, x), idx), x) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( array_inside_qf_bv ) {

  const unsigned elem_width = 8;

  unsigned const index_width = 4; // 16 entries
  const unsigned size = 1<< index_width;
  
  array memory = new_array(elem_width, index_width);

  bitvector index = new_bitvector(index_width);
  ContextType::result_type r = metaSMT::evaluate(ctx, index);
  for (unsigned u = 0; u < size; ++u) {
    r = evaluate(ctx, concat(r, select(memory, 
          bvadd(index, bvuint(u, index_width))
        )));
  }
}

BOOST_AUTO_TEST_CASE( malloc_test )
{
  unsigned const elem_width = 32;
  unsigned const index_width = 4;

  bitvector idx = new_bitvector(index_width);
  assertion( ctx, equal(idx, bvuint(0, index_width)) );

  array mem = new_array(elem_width, index_width);
  bitvector val = new_bitvector(elem_width*4);

//  assertion(ctx, equal(val, concat(select(mem, idx),
//          concat(select(mem, idx),
//            concat(select(mem, idx),
//              select(mem, idx))
//            )
//          )
//        )
//      );
#if 1
  assertion(ctx, equal(val, concat(select(mem, idx),
          concat(select(mem, bvadd(idx, bvuint(1, index_width))),
            concat(select(mem, bvadd(idx, bvuint(2, index_width))),
              select(mem, bvadd(idx, bvuint(3, index_width))))))));
#endif
  BOOST_REQUIRE( solve(ctx) );

  std::cout << read_value(ctx, val) << std::endl;
} 

BOOST_AUTO_TEST_CASE( uninitialized_select )
{
  unsigned const elem_width = 32;
  unsigned const index_width = 4;

  bitvector val = new_bitvector(elem_width);

  array mem;
  bitvector idx = new_bitvector(index_width);
  assertion(ctx, equal(idx, bvuint(0,index_width))); 
  
  BOOST_CHECK_THROW( assertion(ctx, equal(val, select(mem, idx))), std::exception);
}

BOOST_AUTO_TEST_SUITE_END() //Array



//  vim: ft=cpp:ts=2:sw=2:expandtab
