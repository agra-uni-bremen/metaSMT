#include <metaSMT/frontend/QF_BV.hpp>
#include <boost/test/unit_test.hpp>
#include <boost/dynamic_bitset.hpp>
#include <string>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::logic;
using namespace metaSMT::logic::QF_BV;
namespace proto = boost::proto;
using boost::dynamic_bitset;

BOOST_FIXTURE_TEST_SUITE(QF_BV, Solver_Fixture )

BOOST_AUTO_TEST_CASE( negative_t )
{
   const char w = 32;

   bitvector x = new_bitvector(w);
   BOOST_REQUIRE( solve(ctx) );

   assertion( ctx, equal(bvsint(-1, w), x) );

   BOOST_REQUIRE( solve(ctx) );

   int xd = read_value(ctx, x);
   BOOST_CHECK_EQUAL(xd, -1);
}

BOOST_AUTO_TEST_CASE( negative_multiply_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);

  BOOST_REQUIRE( solve(ctx) );

  assertion( ctx, equal( x, bvmul( bvsint(1, w), bvsint(-1, w) ) ) ); 

  BOOST_REQUIRE( solve(ctx) );

  signed char xd = read_value(ctx, x);
  BOOST_CHECK_EQUAL( (int) xd, (int)-1 );
}

BOOST_AUTO_TEST_CASE( simple_sat )
{
  BOOST_REQUIRE( solve(ctx) );
  // sat
  assertion( ctx, equal(bit1,bit1));
  BOOST_REQUIRE( solve(ctx) );

  assertion( ctx, equal(bit1, bvuint(1,1)) );
  BOOST_REQUIRE( solve(ctx) );
  assertion( ctx, equal(bit1, bvsint(-1,1)) );
  BOOST_REQUIRE( solve(ctx) );

  assertion( ctx, equal(bit1, bvbin("1")) );
  BOOST_REQUIRE( solve(ctx) );

  // unsat
  assumption( ctx, equal(bit1, bit0) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, equal(bit1, bvuint(0,1)) );
  BOOST_REQUIRE( !solve(ctx) );
  assumption( ctx, equal(bit1, bvsint(0,1)) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, equal(bit1, bvbin("0")) );
  BOOST_REQUIRE( !solve(ctx) );

}

BOOST_AUTO_TEST_CASE( incremental )
{
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, equal(bit0, bit1));
  BOOST_REQUIRE( !solve(ctx) );
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( equal_t )
{
  bitvector x = new_bitvector(1);
  bitvector y = new_bitvector(1);
  // equal
  assumption( ctx, equal(x, x));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, equal(x, x));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, equal(x, bit1));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, equal(x, bit0));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, equal(x, y));
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(bit1, bvnot(bit0)) );
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, equal(bit0, bvnot(bit1)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(bit0, bvnot(bvnot(bit0))) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(bit1, bvnot(bvnot(bit1))) );
  BOOST_REQUIRE( solve(ctx) );

  // nequal
  assumption( ctx, equal(bit1, bit0));
  BOOST_REQUIRE( !solve(ctx) );
  assumption( ctx, equal(bit0, bit1));
  BOOST_REQUIRE( !solve(ctx) );
  assumption( ctx, equal(x, bvnot(x)));
  BOOST_REQUIRE( !solve(ctx) );
  assumption( ctx, equal(bvnot(x), x));
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( nequal_t )
{
  bitvector x = new_bitvector(1);
  bitvector y = new_bitvector(1);
  // equal
  assumption( ctx, nequal(x, x));
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, nequal(bit1, bvnot(bit0)) );
  BOOST_REQUIRE( !solve(ctx) );
  assumption( ctx, nequal(bit0, bvnot(bit1)) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, nequal(bit0, bvnot(bvnot(bit0))) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, nequal(bit1, bvnot(bvnot(bit1))) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, nequal(x, y));
  BOOST_REQUIRE( solve(ctx) );

  // nequal
  assumption( ctx, nequal(x, bit1));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, nequal(x, bit0));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, nequal(bit1, bit0));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, nequal(bit0, bit1));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, nequal(x, bvnot(x)));
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, nequal(bvnot(x), x));
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( bin_constant_t )
{

  assumption(ctx, equal( bvbin("0"), bvuint(0, 1) ) );
  BOOST_REQUIRE( solve(ctx) );

  assumption(ctx, equal( bvbin("1"), bvuint(1, 1) ) );
  BOOST_REQUIRE( solve(ctx) );

  assumption(ctx, equal( bvbin("0000"), bvuint(0, 4) ) );
  BOOST_REQUIRE( solve(ctx) );

  assumption(ctx, equal( bvbin("0011"), bvuint(3, 4) ) );
  BOOST_REQUIRE( solve(ctx) );

  assumption(ctx, equal( bvbin("1010"), bvuint(10, 4) ) );
  BOOST_REQUIRE( solve(ctx) );

  assumption(ctx, equal( bvbin("1111"), bvuint(15, 4) ) );
  BOOST_REQUIRE( solve(ctx) );

  assumption(ctx, equal( bvbin("11111111"), bvuint(255,8) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, nequal( bvbin("11111111"), bvuint(255,8) ) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption(ctx, equal( bvbin("11110000"), bvuint(240,8) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, nequal( bvbin("11110000"), bvuint(240,8) ) );
  BOOST_REQUIRE( !solve(ctx) );

  bitvector x = new_bitvector(8);

  assumption(ctx, equal( x,  bvbin("10100011") ) );
  BOOST_REQUIRE( solve(ctx) );
  unsigned u = read_value(ctx, x);
  BOOST_REQUIRE_EQUAL( u, 163u);
  assumption(ctx, nequal( bvbin("10100011"), bvuint(163,8) ) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( hex_constant_t )
{

  assumption(ctx, equal( bvhex("0"), bvuint(0, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("1"), bvuint(1, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("2"), bvuint(2, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("3"), bvuint(3, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("4"), bvuint(4, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("5"), bvuint(5, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("6"), bvuint(6, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("7"), bvuint(7, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("8"), bvuint(8, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("9"), bvuint(9, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("a"), bvuint(10, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("A"), bvuint(10, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("b"), bvuint(11, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("B"), bvuint(11, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("c"), bvuint(12, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("C"), bvuint(12, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("d"), bvuint(13, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("D"), bvuint(13, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("e"), bvuint(14, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("E"), bvuint(14, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("f"), bvuint(15, 4) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, equal( bvhex("F"), bvuint(15, 4) ) );
  BOOST_REQUIRE( solve(ctx) );




  bitvector x = new_bitvector(8);
  assumption(ctx, equal( bvhex("FF"), bvbin("11111111") ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, nequal( bvhex("FF"), bvbin("11111111") ) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption(ctx, equal( bvhex("F0"), bvuint(240,8) ) );
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, nequal( bvhex("F0"), bvuint(240,8) ) );
  BOOST_REQUIRE( !solve(ctx) );


  assumption(ctx, equal( x,  bvhex("A3") ) );
  BOOST_REQUIRE( solve(ctx) );
  unsigned u = read_value(ctx, x);
  BOOST_REQUIRE_EQUAL( u, 163u);
  assumption(ctx, nequal( bvhex("A3"), bvuint(163,8) ) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( read_value_eq_t )
{
  using namespace boost::logic;

  bitvector x = new_bitvector(1);
  bitvector y = new_bitvector(1);

  assertion( ctx, equal(x, y) );

  BOOST_REQUIRE( solve(ctx) );

  // bool value
  bool xb = read_value (ctx, x);
  bool yb = read_value (ctx, y);

  BOOST_CHECK_EQUAL( xb, yb );

  // vector bool
  vector<bool> xvb = read_value(ctx, x);
  vector<bool> yvb = read_value(ctx, y);

  BOOST_CHECK( xvb.size() == 1u );
  BOOST_CHECK( yvb.size() == 1u );
  BOOST_CHECK_EQUAL( xvb.at(0), yvb.at(0) );

  // vector tribool
  vector<tribool> xvt = read_value(ctx, x);
  vector<tribool> yvt = read_value(ctx, y);
 
  BOOST_CHECK_EQUAL( xvt.size(), 1u );
  BOOST_CHECK_EQUAL( yvt.size(), 1u );
  BOOST_CHECK_EQUAL( xvt.at(0), yvt.at(0) );
  
  // dynamic_bitset
  dynamic_bitset<> xd = read_value(ctx, x);
  dynamic_bitset<> yd = read_value(ctx, y);
  BOOST_CHECK_EQUAL( xd.size(), 1u );
  BOOST_CHECK_EQUAL( yd.size(), 1u );
  BOOST_CHECK_EQUAL( xd[0], yvt[0] );

  // string
  string xs = read_value(ctx, x);
  string ys = read_value(ctx, y);
  BOOST_CHECK_EQUAL( xs, ys );
}

BOOST_AUTO_TEST_CASE( read_value_t )
{
  using namespace boost::logic;

  bitvector x = new_bitvector(1);
  bitvector y = new_bitvector(1);

  assertion( ctx, nequal(x, y) );
  // add some constraints so that it will not be optimized away
  assertion( ctx, equal(equal(x,x),equal(y,y)) );

  BOOST_REQUIRE( solve(ctx) );

  // bool value
  bool xb = read_value (ctx, x);
  bool yb = read_value (ctx, y);

  BOOST_CHECK_NE( xb, yb );

  // vector bool
  vector<bool> xvb = read_value(ctx, x);
  vector<bool> yvb = read_value(ctx, y);

  BOOST_CHECK_EQUAL( xvb.size(), 1u );
  BOOST_CHECK_EQUAL( yvb.size(), 1u );
  BOOST_CHECK_NE( xvb.at(0), yvb.at(0) );

  // vector tribool
  vector<tribool> xvt = read_value(ctx, x);
  vector<tribool> yvt = read_value(ctx, y);
 
  BOOST_CHECK_EQUAL( xvt.size(), 1u );
  BOOST_CHECK_EQUAL( yvt.size(), 1u );
  BOOST_CHECK_NE( xvt.at(0), yvt.at(0) );

  // dynamic_bitset
  dynamic_bitset<> xd = read_value(ctx, x);
  dynamic_bitset<> yd = read_value(ctx, y);
  BOOST_CHECK_EQUAL( xd.size(), 1u );
  BOOST_CHECK_EQUAL( yd.size(), 1u );
  BOOST_CHECK_NE( xd[0], yvt[0] );

  // string
  string xs = read_value(ctx, x);
  string ys = read_value(ctx, y);
  BOOST_CHECK_NE( xs, ys );
}

BOOST_AUTO_TEST_CASE( bvand_t )
{
  using namespace boost::logic;

  bitvector x = new_bitvector(2);
  bitvector y = new_bitvector(2);
  bitvector z = new_bitvector(2);
  short xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvand(x,y), z) );
  assumption( ctx, equal( z, bvbin("01")) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_CHECK_EQUAL( (xd&yd), zd);

}

BOOST_AUTO_TEST_CASE( bvneg_t )
{
  using namespace boost::logic;

  bitvector x = new_bitvector(8);

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvneg(bvneg(x)), x) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, nequal( bvneg(bvneg(x)), x) );
  BOOST_REQUIRE( !solve(ctx) );
  
  assumption( ctx, equal( bvneg(x), bvadd(bvnot(x), bvuint(1,8))) );
  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, nequal( bvneg(x), bvadd(bvnot(x), bvuint(1,8))) );
  BOOST_REQUIRE( !solve(ctx) );
  
  
  assumption(ctx, equal( bvneg( bvuint(87, 8)), bvsint(-87, 8)));
  BOOST_REQUIRE( solve(ctx) );
  assumption(ctx, nequal( bvneg( bvuint(87, 8)), bvsint(-87, 8)));
  BOOST_REQUIRE( !solve(ctx) );


}

BOOST_AUTO_TEST_CASE( bvnand_t )
{
  using namespace boost::logic;

  const unsigned w = sizeof(short)*8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  dynamic_bitset<> xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvnand(x,y), z) );
  assumption( ctx, equal( z, bvuint(1, w)) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_CHECK_EQUAL( ~(xd&yd), zd);
}

BOOST_AUTO_TEST_CASE( bvor_t )
{
  using namespace boost::logic;

  bitvector x = new_bitvector(2);
  bitvector y = new_bitvector(2);
  bitvector z = new_bitvector(2);
  dynamic_bitset<> xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvor(x,y), z) );
  assumption( ctx, equal( z, bvbin("01")) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_CHECK_EQUAL( (xd|yd), zd);
}

BOOST_AUTO_TEST_CASE( bvxor_t )
{
  using namespace boost::logic;

  bitvector x = new_bitvector(2);
  bitvector y = new_bitvector(2);
  bitvector z = new_bitvector(2);
  dynamic_bitset<> xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvxor(x,y), z) );
  assumption( ctx, equal( z, bvbin("10")) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_CHECK_EQUAL( (xd^yd), zd);

}

BOOST_AUTO_TEST_CASE( bvnor_t )
{
  using namespace boost::logic;

  bitvector x = new_bitvector(2);
  bitvector y = new_bitvector(2);
  bitvector z = new_bitvector(2);
  dynamic_bitset<> xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvnor(x,y), z) );
  assumption( ctx, equal( z, bvbin("10")) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_CHECK_EQUAL( ~(xd|yd), zd);

}

BOOST_AUTO_TEST_CASE( bvxnor_t )
{
  using namespace boost::logic;

  bitvector x = new_bitvector(2);
  bitvector y = new_bitvector(2);
  bitvector z = new_bitvector(2);
  dynamic_bitset<> xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvxnor(x,y), z) );
  assumption( ctx, equal( z, bvbin("10")) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_CHECK_EQUAL( (~xd^yd), zd);

}

BOOST_AUTO_TEST_CASE( bvadd_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  unsigned char xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvadd(x,y), z) );
  assumption( ctx, equal( z, bvuint(135, w)) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  unsigned char r = xd+yd;

  BOOST_REQUIRE_EQUAL( 135, zd);
  BOOST_CHECK_EQUAL( r, zd);

}

BOOST_AUTO_TEST_CASE( bvsub_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  unsigned char xd, yd, zd, r;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvsub(x,y), z) );
  assumption( ctx, equal( z, bvuint(135, w)) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  r = xd-yd;
  BOOST_REQUIRE_EQUAL( 135, zd);
  BOOST_CHECK_EQUAL( r, zd);

}

BOOST_AUTO_TEST_CASE( bvsub_2 )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);

  unsigned xd, yd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvadd(bvsub(x,y),y), x) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);

  BOOST_CHECK_EQUAL( (xd-yd)+yd, xd );

  assumption( ctx, nequal( bvadd(bvsub(x,y),y), x) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( bvmul_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  unsigned char xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvmul(x,y), z) );
  assumption( ctx, equal( z, bvuint(135, w)) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  unsigned char r = xd*yd;

  BOOST_REQUIRE_EQUAL( 135, zd);
  BOOST_CHECK_EQUAL( r, zd);
}

BOOST_AUTO_TEST_CASE( bvudiv_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  unsigned char xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvudiv(x,y), z) );
  assumption( ctx, nequal( bvuint(0,w), y) );
  assumption( ctx, equal( z, bvuint(7, w)) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_REQUIRE_NE( yd, 0);
  unsigned char r = xd/yd;

  BOOST_REQUIRE_EQUAL( 7, zd);
  BOOST_CHECK_EQUAL( r, zd);
}

BOOST_AUTO_TEST_CASE( bvudiv_250_1 )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  unsigned char xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, equal( bvudiv(x,y), z) );
  assumption( ctx, equal( bvuint(1,w), y) );
  assumption( ctx, equal( bvuint(250,w), x) );
  BOOST_REQUIRE( solve(ctx) );
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);


  BOOST_REQUIRE_NE( yd, 0);
  unsigned char r = xd/yd;

  BOOST_CHECK_EQUAL( (unsigned)r, (unsigned)zd);
}


BOOST_AUTO_TEST_CASE( bvudiv_2 )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  unsigned char xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );
  
  assumption( ctx, equal( bvudiv(x,y), z) );
  
  assumption( ctx, nequal( bvuint(0,w), y) );
 // assumption( ctx, equal( bvuint(7,w), x) );
  assumption( ctx, nequal( bvuint(0,w), y) );
//  assumption( ctx, equal( bvuint(35,w), y) );
  //assumption( ctx, equal( bvuint(2,w), y) );

  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);

  yd = read_value(ctx, y);
  zd = read_value(ctx, z);


  BOOST_REQUIRE_NE( yd, 0);
  unsigned char r = xd/yd;

  //BOOST_REQUIRE_EQUAL( 7, zd);
  
  BOOST_CHECK_EQUAL( (unsigned)r, (unsigned)zd);
}


BOOST_AUTO_TEST_CASE( bvudiv_3 )
{
  using namespace boost::logic;

  const char w = 6;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  unsigned char xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );
  assumption( ctx, equal( bvudiv(x,y), z) );
  assumption( ctx, nequal( bvuint(0,w), y) );
  BOOST_REQUIRE( solve(ctx) );
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);


  BOOST_REQUIRE_NE( yd, 0);
  unsigned char r = xd/yd;

  BOOST_CHECK_EQUAL( (unsigned)r, (unsigned)zd);
}


BOOST_AUTO_TEST_CASE( bvsdiv_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  signed char xd, yd, zd, r;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvsdiv(x,y), z) );
  assumption( ctx, nequal( bvsint(0,w), y) );
  assumption( ctx, equal( z, bvsint(7, w)) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_REQUIRE_NE( yd, 0);
  r = xd/yd;

  BOOST_REQUIRE_EQUAL( 7, zd);
  BOOST_CHECK_EQUAL( static_cast<int>(r), static_cast<int>(zd) );

  assumption( ctx, equal( bvsdiv(x,y), z) );
  assumption( ctx, nequal( bvsint(0,w), y) );
  assumption( ctx, equal( z, bvsint(-7, w)) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  r = xd/yd;

  BOOST_REQUIRE_EQUAL( -7, zd);
  BOOST_CHECK_EQUAL( r, zd);
}

BOOST_AUTO_TEST_CASE( bvsdiv_39_5 )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  signed char xd, yd, zd, r;

  BOOST_REQUIRE( solve(ctx) );

  assertion ( ctx, equal( bvsdiv(x,y), z) );

  assumption( ctx, equal( bvsint(39, w), x) );
  assumption( ctx, equal( bvsint( 5, w), y) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_REQUIRE_NE( yd, 0);
  r = xd/yd;


  BOOST_CHECK_EQUAL(  5, static_cast<int>(yd) );
  BOOST_CHECK_EQUAL( 39, static_cast<int>(xd) );

  BOOST_REQUIRE_EQUAL( 7, static_cast<int>(r ) );
  BOOST_REQUIRE_EQUAL( 7, static_cast<int>(zd) );
  BOOST_CHECK_EQUAL( static_cast<int>(r), static_cast<int>(zd) );

  assumption( ctx, equal( bvsint(-39, w), x) );
  assumption( ctx, equal( bvsint( -5, w), y) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_REQUIRE_NE( yd, 0);
  r = xd/yd;

  BOOST_REQUIRE_EQUAL( 7, zd);
  BOOST_CHECK_EQUAL( static_cast<int>(r), static_cast<int>(zd) );

  assumption( ctx, equal( bvsint(39,w), x) );
  assumption( ctx, equal( bvsint(-5, w), y) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_REQUIRE_NE( yd, 0);
  r = xd/yd;

  BOOST_REQUIRE_EQUAL( -7, static_cast<int>(zd));
  BOOST_CHECK_EQUAL( static_cast<int>(r), static_cast<int>(zd) );

  assumption( ctx, equal( bvsint(-39,w), x) );
  assumption( ctx, equal( bvsint(5, w), y) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_REQUIRE_NE( yd, 0);
  r = xd/yd;

  BOOST_REQUIRE_EQUAL( -7, zd);
  BOOST_CHECK_EQUAL( static_cast<int>(r), static_cast<int>(zd) );
}


BOOST_AUTO_TEST_CASE( bvurem_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  unsigned char xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvurem(x,y), z) );
  assumption( ctx, nequal( bvuint(0,w), y) );
  assumption( ctx, equal( z, bvuint(17, w)) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_REQUIRE_NE( yd, 0);
  unsigned char r = xd%yd;

  BOOST_REQUIRE_EQUAL( 17, zd);
  BOOST_CHECK_EQUAL( r, zd);
}

BOOST_AUTO_TEST_CASE( bvsrem_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  signed char xd, yd, zd, rd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal(x, bvuint(3,w)) );
  assumption( ctx, equal(y, bvuint(2,w)) );
  assumption( ctx, equal(z, bvuint(1,w)) );
  assumption( ctx, equal(bvsrem(x, y), z) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_REQUIRE_NE( yd, 0);
  rd = xd % yd;
  BOOST_REQUIRE_EQUAL(zd, rd);

  assumption( ctx, equal(x, bvuint(-1,w)) );
  assumption( ctx, equal(y, bvuint(2,w)) );
  assumption( ctx, equal(z, bvuint(-1,w)) );
  assumption( ctx, equal(bvsrem(x, y), z) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_REQUIRE_NE( yd, 0);
  rd = xd % yd;
  BOOST_REQUIRE_EQUAL(zd, rd);
}

BOOST_AUTO_TEST_CASE( bvurem_2 )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);
  unsigned char xd, yd, zd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvurem(x,y), z) );
  assumption( ctx, nequal( bvuint(0,w), y) );
  assumption( ctx, equal( z, bvuint(17, w)) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  zd = read_value(ctx, z);

  BOOST_REQUIRE_NE( yd, 0);
  unsigned char r = xd%yd;

  BOOST_REQUIRE_EQUAL( 17, zd);
  BOOST_CHECK_EQUAL( r, zd);
}

BOOST_AUTO_TEST_CASE( bvcomp_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  char xd, yd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, equal( bvcomp(x,y), bit1) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);

  BOOST_CHECK_EQUAL(xd, yd);

  assumption( ctx, equal( bvcomp(x,y), bit0) );
  BOOST_REQUIRE( solve(ctx) );
  
  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  BOOST_CHECK_NE(xd, yd);
}

BOOST_AUTO_TEST_CASE( bvslt_2 )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  signed char xd, yd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvslt(x,y) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);

  BOOST_CHECK_LT(xd, yd);

  assumption( ctx, Not( bvslt(x,y) ) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);

  BOOST_CHECK_GE(xd, yd);
}





BOOST_AUTO_TEST_CASE( bvslt_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  signed char xd, yd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvslt(x,y) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);

  BOOST_CHECK_LT(xd, yd);

  assumption( ctx, Not( bvslt(x,y) ) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  BOOST_CHECK_GE(xd, yd);
}

BOOST_AUTO_TEST_CASE( bvsgt_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  signed char xd, yd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvsgt(x,y) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);

  BOOST_CHECK_GT(xd, yd);

  assumption( ctx, Not( bvsgt(x,y) ) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  BOOST_CHECK_LE(xd, yd);
}

BOOST_AUTO_TEST_CASE( bvsle_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  signed char xd, yd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvsle(x,y) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);

  BOOST_CHECK_LE(xd, yd);

  assumption( ctx, Not( bvsle(x,y) ) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  BOOST_CHECK_GT(xd, yd);
}


BOOST_AUTO_TEST_CASE( bvsge_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  signed char xd, yd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvsge(x,y) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);

  BOOST_CHECK_GE(xd, yd);

  assumption( ctx, Not( bvsge(x,y) ) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  BOOST_CHECK_LT(xd, yd);
}

BOOST_AUTO_TEST_CASE( bvult_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  unsigned char xd, yd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvult(x,y) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);

  //printf("%u %u\n",xd, yd);
  BOOST_CHECK_LT(xd, yd);

  assumption( ctx, Not( bvult(x,y) ) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  BOOST_CHECK_GE(xd, yd);
  //printf("%u %u\n",xd, yd);
}

BOOST_AUTO_TEST_CASE( bvult_all )
{
  using namespace boost::logic;

  const char w = 4;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  unsigned xd, yd;

  BOOST_REQUIRE( solve(ctx) );

  assertion( ctx, bvult(x,y) );
  
  unsigned limit = 257;
  
  while( solve(ctx) ) {
    if( --limit == 0) break;
    xd = read_value(ctx, x);
    yd = read_value(ctx, y);
    //printf("%u %u\n",xd, yd);
    BOOST_REQUIRE_LT(xd, yd);
  
    assertion( ctx, Nand( equal(x, bvuint(xd,w)), equal(y, bvuint(yd, w)) ) );
  
  }
}

BOOST_AUTO_TEST_CASE( bvugt_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  unsigned char xd, yd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvugt(x,y) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);

  BOOST_CHECK_GT(xd, yd);

  assumption( ctx, Not( bvugt(x,y) ) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  BOOST_CHECK_LE(xd, yd);
}

BOOST_AUTO_TEST_CASE( bvule_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  unsigned char xd, yd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvule(x,y) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);

  BOOST_CHECK_LE(xd, yd);

  assumption( ctx, Not( bvule(x,y) ) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  BOOST_CHECK_GT(xd, yd);
}

BOOST_AUTO_TEST_CASE( bvule_70 )
{
  using namespace boost::logic;

  const char w = 8;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvule( bvuint(70,w), bvuint(70,w)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, Not(bvule( bvuint(70,w), bvuint(70,w)) ) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, bvule( bvuint(69,w), bvuint(70,w)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, Not(bvule( bvuint(69,w), bvuint(70,w)) ) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, bvule( bvuint(71,w), bvuint(70,w)) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, Not(bvule( bvuint(71,w), bvuint(70,w)) ) );
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( bvule_1 )
{
  using namespace boost::logic;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvule( bit1, bit1) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, Not(bvule( bit1,bit1) ) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, bvule( bit0, bit1) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, Not(bvule( bit0, bit1) ) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, bvule( bit1, bit0) );
  BOOST_REQUIRE( !solve(ctx) );
  
  assumption( ctx, Not(bvule( bit1, bit0) ));
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvule( bit0, bit0) );
  BOOST_REQUIRE( solve(ctx) );
  
  assumption( ctx, Not(bvule( bit0, bit0) ));
  BOOST_REQUIRE( !solve(ctx) );
  
}

BOOST_AUTO_TEST_CASE( bvule_2 )
{
  using namespace boost::logic;

  const char w = 2;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvule( bvuint(2,w), bvuint(2,w)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, Not(bvule( bvuint(2,w), bvuint(2,w)) ) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, bvule( bvuint(1,w), bvuint(2,w)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, Not(bvule( bvuint(1,w), bvuint(2,w)) ) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, bvule( bvuint(3,w), bvuint(2,w)) );
  BOOST_REQUIRE( !solve(ctx) );

  assumption( ctx, Not(bvule( bvuint(3,w), bvuint(2,w)) ) );
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( bvuge_t )
{
  using namespace boost::logic;

  const char w = 8;

  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  unsigned char xd, yd;

  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, bvuge(x,y) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);

  BOOST_CHECK_GE(xd, yd);

  assumption( ctx, Not( bvuge(x,y) ) );
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  yd = read_value(ctx, y);
  BOOST_CHECK_LT(xd, yd);
}

BOOST_AUTO_TEST_CASE( predicate_bvslt )
{
   const char w = 8;

   bitvector x = new_bitvector(w);
   bitvector y = new_bitvector(w);
   predicate p = new_variable();
   predicate q = new_variable();
   bool pd;
   bool qd;

   BOOST_REQUIRE( solve(ctx) );

   assertion( ctx, equal(p, bvslt(x,y)) );
   assertion( ctx, equal(p, True) );
   BOOST_REQUIRE( solve(ctx) );

   pd = read_value(ctx, p);

   BOOST_CHECK_EQUAL(pd, true);

   assertion( ctx, equal(q, Not( bvslt(x,y) ) ) );
   BOOST_REQUIRE( solve(ctx) );

   qd = read_value(ctx, q);

   BOOST_CHECK_EQUAL(qd, false);
}

BOOST_AUTO_TEST_CASE( uninitialized_readt )
{
   const char w = 8;

   bitvector x = new_bitvector(w);
   signed char xd;

   BOOST_REQUIRE( solve(ctx) );

   xd = read_value(ctx, x);

   BOOST_CHECK_EQUAL(xd, xd);
}

/**
 * this tests triggers an invalid optimization
 * is SWORD, the constrained is preprocessed,
 * found to constant true and replaced with
 * true. Therefore no assignment for the 
 * variables is generated.
 */
BOOST_AUTO_TEST_CASE( keeps_tiny_assertions )
{
   const char w = 32;

   bitvector retval = new_bitvector(w);
   assertion( ctx, equal(retval, retval));

   BOOST_REQUIRE( solve(ctx) );
   
   bitvector tmp0 = new_bitvector(w);
   assertion( ctx, equal(tmp0, tmp0));

   BOOST_REQUIRE( solve(ctx) );

   bitvector x = new_bitvector(w);
   assertion( ctx, equal(x, x));

   assertion( ctx, equal(bvuint(3, w), x));

   BOOST_REQUIRE( solve(ctx) );

   bitvector tmp1 = new_bitvector(w);
   assertion( ctx, equal(tmp1, x));

   assertion( ctx, equal(tmp1, tmp0));

   BOOST_REQUIRE( solve(ctx) );

   unsigned xd = read_value(ctx, x);
   unsigned tmp0d = read_value(ctx, tmp0);
   unsigned tmp1d = read_value(ctx, tmp1);

   BOOST_CHECK_EQUAL(xd, 3u);
   BOOST_CHECK_EQUAL(tmp0d, 3u);
   BOOST_CHECK_EQUAL(tmp1d, 3u);
}

BOOST_AUTO_TEST_CASE( keeps_small_assertions )
{
   const char w = 32;

   bitvector tmp0   = new_bitvector(w);
   bitvector tmp1   = new_bitvector(w);
   bitvector x      = new_bitvector(w);
   BOOST_REQUIRE( solve(ctx) );

   assertion( ctx, And(And( equal(bvuint(3, w), x),
                   equal(tmp1, tmp0)),
                   equal(tmp1, x)));

   BOOST_REQUIRE( solve(ctx) );

   unsigned xd = read_value(ctx, x);
   unsigned tmp0d = read_value(ctx, tmp0);
   unsigned tmp1d = read_value(ctx, tmp1);

   BOOST_CHECK_EQUAL(xd, 3u);
   BOOST_CHECK_EQUAL(tmp0d, 3u);
   BOOST_CHECK_EQUAL(tmp1d, 3u);
}

BOOST_AUTO_TEST_CASE( negative_multiply_t2 )
{
   using namespace boost::logic;

   const unsigned w = 8;

   bitvector x = new_bitvector(w);
   bitvector y = new_bitvector(w);
   bitvector z = new_bitvector(w);

   BOOST_REQUIRE( solve(ctx) );

   assertion( ctx, equal( y, bvsint( -1, w) ));
   assertion( ctx, equal( z, bvsint(  1, w) ));
   assertion( ctx, equal( x, bvmul (  z, y) ));
   BOOST_REQUIRE( solve(ctx) );

   signed char xd = read_value(ctx, x);
   signed char yd = read_value(ctx, y);
   signed char zd = read_value(ctx, z);
   BOOST_CHECK_EQUAL( yd, -1 );
   BOOST_CHECK_EQUAL( zd,  1 );
   BOOST_CHECK_EQUAL( xd, -1 );
}

BOOST_AUTO_TEST_CASE( ite_t )
{
   using namespace boost::logic;

   const unsigned w = 8;

   predicate c = new_variable();
   bitvector x = new_bitvector(w);
   bitvector y = new_bitvector(w);
   bitvector z = new_bitvector(w);

   BOOST_REQUIRE( solve(ctx) );

   assertion( ctx, equal( x, Ite( c, y, z) ));

   assumption( ctx, c);

   BOOST_REQUIRE( solve(ctx) );

   bool b = read_value(ctx, c);
   int xd = read_value(ctx, x);
   int yd = read_value(ctx, y);
   int zd = read_value(ctx, z);

   BOOST_CHECK_EQUAL( b, true );
   BOOST_CHECK_EQUAL( xd, yd );
   
   assumption( ctx, Not(c) );

   BOOST_REQUIRE( solve(ctx) );

   b  = read_value(ctx, c);
   xd = read_value(ctx, x);
   yd = read_value(ctx, y);
   zd = read_value(ctx, z);

   BOOST_CHECK_EQUAL( b, false );
   BOOST_CHECK_EQUAL( xd, zd );
}

BOOST_AUTO_TEST_CASE( concat_extract_x )
{
   const unsigned w = 8;

   bitvector x = new_bitvector(w);
   bitvector y = new_bitvector(w);

   BOOST_REQUIRE( solve(ctx) );

   assertion( ctx, equal( x, extract( 7, 0, concat(x, y) )) );

   BOOST_REQUIRE( solve(ctx) );

   assertion( ctx, nequal( x, extract( 7, 0, concat(x, y) )) );

   BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( concat_extract_y )
{
   const unsigned w = 8;

   bitvector x = new_bitvector(w);
   bitvector y = new_bitvector(w);
   assertion( ctx, equal( y, extract( 15, 8, concat(x, y) )) );

   BOOST_REQUIRE( solve(ctx) );

   assertion( ctx, nequal( y, extract( 15, 8, concat(x, y) )) );

   BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( bvshl_t )
{
   const unsigned w = 32;
   bitvector x = new_bitvector(w);

   BOOST_REQUIRE( solve(ctx) );

   assertion( ctx, equal( bvmul(x, bvuint(2,w)), bvshl( x, bvuint(2,w))) );
   BOOST_REQUIRE( solve(ctx) );

   assertion( ctx, nequal( bvmul(x, bvuint(2,w)), bvshl( x, bvuint(2,w))) );
   BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( bvshl_all )
{
  const unsigned w = 16;
  bitvector x = new_bitvector(w);
  bitvector y = new_bitvector(w);
  bitvector z = new_bitvector(w);

  const unsigned xlimit = 256;
  const unsigned ylimit = w;
  BOOST_REQUIRE( solve(ctx) );
  assertion(ctx, equal( z, bvshl( x, y)) );
  assertion(ctx, bvult(x,bvuint(xlimit,w)));
  assertion(ctx, bvult(y,bvuint(ylimit,w)));
  
  unsigned limit = xlimit*ylimit+1;

  while( solve(ctx) ) {
    if( --limit == 0) break;
    unsigned xd = read_value(ctx, x);
    unsigned yd = read_value(ctx, y);
    unsigned zd = read_value(ctx,z);

    //printf("before shifting: %d %u %u %u\n",limit, xd, yd, zd);
    
    unsigned shifted = (xd << yd) %(1ul << w);

    //printf("after shifting: %d %u %u %u\n",limit, xd, yd, zd);

    //std::cout << "x: " <<read_value(ctx,x) << std::endl;
    //std::cout << "y: " <<read_value(ctx,y) << std::endl;
    //std::cout << "z: " <<read_value(ctx,z) << std::endl;
    BOOST_REQUIRE_EQUAL(shifted, zd);

    //printf("test: %d %u %u %u\n",limit, xd, yd, zd);

    assertion( ctx, Nand( equal(x, bvuint(xd,w)), equal(y, bvuint(yd, w)) ) );
    
  }
  BOOST_REQUIRE_EQUAL(limit,1u);
}

BOOST_AUTO_TEST_CASE( bvshl_128_30 )
{
   const unsigned w = 32;
   bitvector x = new_bitvector(w);
   bitvector y = new_bitvector(w);
   bitvector z = new_bitvector(w);

   BOOST_REQUIRE( solve(ctx) );

   assumption(ctx, equal( z, bvshl( x, y)) );
   assumption(ctx, equal(x, bvuint(128,w)));
   assumption(ctx, equal(y, bvuint( 30,w)));
   assumption(ctx, equal(z, bvuint(  0,w)));
   BOOST_REQUIRE( solve(ctx) );

   assumption(ctx, nequal( z, bvshl( x, y)) );
   assumption(ctx, equal(x, bvuint(128,w)));
   assumption(ctx, equal(y, bvuint( 30,w)));
   assumption(ctx, equal(z, bvuint(  0,w)));
   BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( bvshr_t )
{
   const unsigned w = 32;
   BOOST_REQUIRE( solve(ctx) );

   assumption( ctx, equal( bvuint(1,w), bvshr(bvuint(8,w), bvuint(3, w))) );
   BOOST_REQUIRE( solve(ctx) );

   assumption( ctx, nequal( bvuint(1,w), bvshr(bvuint(8,w), bvuint(3, w))) );
   BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( bvashr_t )
{
   const unsigned w = 32;
   bitvector x = new_bitvector(w);
   BOOST_REQUIRE( solve(ctx) );

   assumption( ctx, equal( bvsint(-1,w), bvashr(bvsint(-1,w), x)) );
   BOOST_REQUIRE( solve(ctx) );

   assumption( ctx, nequal( bvsint(-1,w), bvashr(bvsint(-1,w), x)) );
   BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( zero_extend_t )
{
   const unsigned w = 8;
   BOOST_REQUIRE( solve(ctx) );

   assertion( ctx, equal( zero_extend(w, bvuint(255,w)), bvuint(255,2*w)));
   BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( sign_extend_t )
{
   const unsigned w = 8;
   BOOST_REQUIRE( solve(ctx) );

   assertion( ctx, equal( sign_extend(w, bvsint(-1,w)), bvsint(-1,2*w)));
   BOOST_REQUIRE( solve(ctx) );
}


BOOST_AUTO_TEST_CASE( evaluate_concat )
{
  const unsigned w = 8;
  BOOST_REQUIRE( solve(ctx) );

  bitvector x = new_bitvector(w);
  bitvector x2 = new_bitvector(2*w);

  ContextType::result_type cc = evaluate( ctx, concat(x,x) );

  metaSMT::assertion( ctx, metaSMT::logic::equal( x2, cc) );
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( read_value_constant )
{
  const unsigned w = 32;
  bitvector x = new_bitvector(w);

  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( x, bvuint(13,w) ) );
  BOOST_REQUIRE( solve(ctx) );
  unsigned i = read_value(ctx, x);
  BOOST_CHECK_EQUAL( i, 13u);
  
  std::string s = read_value(ctx, x);
  BOOST_CHECK_EQUAL( s, "00000000000000000000000000001101");

}

BOOST_AUTO_TEST_CASE( bvint_t )
{
  const unsigned w = 32;

  BOOST_REQUIRE( solve(ctx) );
  metaSMT::assumption( ctx, metaSMT::logic::equal( bvuint(13,w), bvint(13u,w) ) );
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::nequal( bvuint(13,w), bvint(13u,w) ) );
  BOOST_REQUIRE( !solve(ctx) );
  
  metaSMT::assumption( ctx, metaSMT::logic::equal( bvsint(13,w), bvint(13,w) ) );
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::nequal( bvsint(13,w), bvint(13,w) ) );
  BOOST_REQUIRE( !solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvsint(-13,w), bvint(-13,w) ) );
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::nequal( bvsint(-13,w), bvint(-13,w) ) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( bvuint_t )
{
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvuint(123,8),
    bvbin("01111011")
  ));
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvuint(0x5F55,16),
    bvbin("01011111" "01010101")
  ));
  BOOST_REQUIRE( solve(ctx) );
  
  metaSMT::assumption( ctx, metaSMT::logic::equal( bvuint(0x555F55F5,32),
    bvbin("01010101" "01011111" "01010101" "11110101")
  ));
  BOOST_REQUIRE( solve(ctx) );
  
  metaSMT::assumption( ctx, metaSMT::logic::equal( bvuint(0x555F55555F55F555ul,64),
    bvbin("01010101" "01011111" "01010101" "01010101"
          "01011111" "01010101" "11110101" "01010101")
  ));
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvuint(0xF5555F555555F555ul,128),
    bvbin("00000000" "00000000" "00000000" "00000000"
          "00000000" "00000000" "00000000" "00000000"
          "11110101" "01010101" "01011111" "01010101"
          "01010101" "01010101" "11110101" "01010101")
  ));
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( bvsint_t )
{
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvsint(123,8),
    bvbin("01111011")
  ));
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvsint(0x5F55,16),
    bvbin("01011111" "01010101")
  ));
  BOOST_REQUIRE( solve(ctx) );
  
  metaSMT::assumption( ctx, metaSMT::logic::equal( bvsint(0x555F55F5,32),
    bvbin("01010101" "01011111" "01010101" "11110101")
  ));
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvsint(0x555F55555F55F555ul,64),
    bvbin("01010101" "01011111" "01010101" "01010101"
          "01011111" "01010101" "11110101" "01010101")
  ));
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvsint(0xF5555F555555F555ul,128),
    bvbin("11111111" "11111111" "11111111" "11111111"
          "11111111" "11111111" "11111111" "11111111"
          "11110101" "01010101" "01011111" "01010101"
          "01010101" "01010101" "11110101" "01010101")
  ));
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvsint(-123,8),
    bvbin("10000101")
  ));
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvsint(-123,16),
    bvbin("11111111" "10000101")
  ));
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvsint(-123,32),
    bvbin("11111111" "11111111" "11111111" "10000101")
  ));
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvsint(-123,64),
    bvbin("11111111" "11111111" "11111111" "11111111"
          "11111111" "11111111" "11111111" "10000101")
  ));
  BOOST_REQUIRE( solve(ctx) );

  metaSMT::assumption( ctx, metaSMT::logic::equal( bvsint(-123,128),
    bvbin("11111111" "11111111" "11111111" "11111111"
          "11111111" "11111111" "11111111" "11111111"
          "11111111" "11111111" "11111111" "11111111"
          "11111111" "11111111" "11111111" "10000101")
  ));
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( variable_equality )
{
  unsigned const width = 8;
  bitvector x = new_bitvector(width);
  bitvector y = new_bitvector(width);

  bool cmp = (x == x);
  BOOST_CHECK( cmp );

  cmp = (x == y);
  BOOST_CHECK( !cmp );

  cmp = (y == x);
  BOOST_CHECK( !cmp );
}

BOOST_AUTO_TEST_CASE( constant_64bit )
{
  unsigned const w = 64;
  unsigned long const value = std::numeric_limits<unsigned long>::max();
  bitvector x = new_bitvector(w);

  assumption(ctx, equal(x, bvuint(value, w)));
  BOOST_REQUIRE( solve(ctx) );

  unsigned long xd = read_value(ctx, x);
  std::string xs = read_value(ctx, x);
  BOOST_CHECK_EQUAL(xd, value);
  BOOST_CHECK_EQUAL(xs, "1111111111111111111111111111111111111111111111111111111111111111");

  assumption(ctx, equal(x, bvuint(value-123, w)));
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  BOOST_CHECK_EQUAL(xd, value-123);
}

BOOST_AUTO_TEST_CASE( constant_69bit )
{
  bitvector x = new_bitvector(69);

  const std::string longconst ("001111001110010101010100000000000000000000000000000000000000000000000");
  assumption(ctx, equal( x,  bvbin(longconst) ) );
  BOOST_REQUIRE( solve(ctx) );
  std::string longval = read_value(ctx, x);
  BOOST_REQUIRE_EQUAL( longconst, longval);
}

BOOST_AUTO_TEST_CASE( signed_constant_64bit )
{
  unsigned const w = 64;
  long value = std::numeric_limits<long>::max();
  bitvector x = new_bitvector(w);

  assumption(ctx, equal(x, bvsint(value, w)));
  BOOST_REQUIRE( solve(ctx) );

  std::string xs = read_value(ctx, x);
  BOOST_CHECK_EQUAL(xs, "0111111111111111111111111111111111111111111111111111111111111111");

  long xd = read_value(ctx, x);
  BOOST_CHECK_EQUAL(xd, value);

  assumption(ctx, equal(x, bvsint(value-123, w)));
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  BOOST_CHECK_EQUAL(xd, value-123);

  value = std::numeric_limits<long>::min();

  assumption(ctx, equal(x, bvsint(value, w)));
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  BOOST_CHECK_EQUAL(xd, value);

  assumption(ctx, equal(x, bvsint(value+123, w)));
  BOOST_REQUIRE( solve(ctx) );

  xd = read_value(ctx, x);
  BOOST_CHECK_EQUAL(xd, value+123);

}


BOOST_AUTO_TEST_CASE(extended_concat) {


  // b[..] == b
  bitvector b_1   = new_bitvector(8);
  bitvector b_0_1 = new_bitvector(4);
  bitvector b_1_1 = new_bitvector(4);
  assertion(ctx, equal( concat( b_1_1, b_0_1), b_1) );

  bitvector a_1   = new_bitvector(8);
  bitvector a_0_1 = new_bitvector(4);
  bitvector a_1_1 = new_bitvector(4);

  // a[..] == a
  assertion(ctx, equal( concat( a_1_1, a_0_1), a_1) );

  bitvector z_1   = new_bitvector(16);
  bitvector z_0_1 = new_bitvector(4);
  bitvector z_1_1 = new_bitvector(4);
  bitvector z_2_1 = new_bitvector(4);
  bitvector z_3_1 = new_bitvector(4);

  // z[..] == z
  assertion(ctx, equal(
    concat( z_3_1,
    concat( z_2_1,
    concat( z_1_1,
            z_0_1))),
    z_1
  ));

  bitvector buf_3_o_0_1 = new_bitvector(4);
  bitvector buf_3_o_1_1 = new_bitvector(4);
  bitvector buf_3_o_2_1 = new_bitvector(4);
  bitvector buf_3_o_3_1 = new_bitvector(4);

  // (a[..],b[..]) == buf
  assertion(ctx, equal(

    concat( a_1_1,
    concat( a_0_1,
    concat( b_1_1,
            b_0_1))),

    concat( buf_3_o_3_1,
    concat( buf_3_o_2_1,
    concat( buf_3_o_1_1,
            buf_3_o_0_1)))
  ));

  // buf[..] == z[..]
  assertion(ctx, equal(

    concat( buf_3_o_3_1,
    concat( buf_3_o_2_1,
    concat( buf_3_o_1_1,
            buf_3_o_0_1))),

    concat( z_3_1,
    concat( z_2_1,
    concat( z_1_1,
            z_0_1)))

  ));


  BOOST_REQUIRE( solve(ctx) );

  // a = 00
  // b = 00
  assumption(ctx, equal(a_1, bvbin("00000000")));
  assumption(ctx, equal(b_1, bvbin("00000000")));

  BOOST_REQUIRE( solve(ctx) );

  std::string av = read_value(ctx, a_1);
  std::string bv = read_value(ctx, b_1);
  std::string zv = read_value(ctx, z_1);

  BOOST_REQUIRE_EQUAL( av, "00000000" );
  BOOST_REQUIRE_EQUAL( bv, "00000000" );
  BOOST_REQUIRE_EQUAL( zv, "0000000000000000" );


  // a = 00
  // b = 01
  assumption(ctx, equal(a_1, bvbin("00000000")));
  assumption(ctx, equal(b_1, bvbin("00000001")));

  BOOST_REQUIRE( solve(ctx) );

  std::string av2 = read_value(ctx, a_1);
  std::string bv2 = read_value(ctx, b_1);
  std::string zv2 = read_value(ctx, z_1);

  BOOST_REQUIRE_EQUAL( av2, "00000000" );
  BOOST_REQUIRE_EQUAL( bv2, "00000001" );
  BOOST_REQUIRE_EQUAL( zv2, "0000000000000001" );


  // a = 01
  // b = 00
  assumption(ctx, equal(a_1, bvbin("00000001")));
  assumption(ctx, equal(b_1, bvbin("00000000")));

  BOOST_REQUIRE( solve(ctx) );

  std::string av3 = read_value(ctx, a_1);
  std::string bv3 = read_value(ctx, b_1);
  std::string zv3 = read_value(ctx, z_1);

  BOOST_REQUIRE_EQUAL( av3, "00000001" );
  BOOST_REQUIRE_EQUAL( bv3, "00000000" );
  BOOST_REQUIRE_EQUAL( zv3, "0000000100000000" );
}

BOOST_AUTO_TEST_SUITE_END() //QF_BV

//  vim: ft=cpp:ts=2:sw=2:expandtab
