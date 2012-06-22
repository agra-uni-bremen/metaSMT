#define BOOST_TEST_MODULE test_result_wrapper
#include <metaSMT/result_wrapper.hpp>

#include <boost/proto/debug.hpp>
#include <boost/test/unit_test.hpp>
#include <string>

using namespace std;
using namespace metaSMT;
using boost::dynamic_bitset;
using boost::logic::tribool;

class Fixture {
  public:

  protected:
};

void check_conversion_1_in_8bit( result_wrapper const & rw)
{
  std::string s = rw;
  BOOST_REQUIRE_EQUAL( s, "00000001" );

  int i = rw;
  BOOST_REQUIRE_EQUAL( i, 1);

  unsigned u = rw;
  BOOST_REQUIRE_EQUAL( u, 1);

  vector<bool> a, b(8, false);
  b[0] = true;
  a = rw;
  BOOST_REQUIRE_EQUAL_COLLECTIONS(a.begin(), a.end(), b.begin(), b.end());

  vector<tribool> tb = rw;
  BOOST_REQUIRE_EQUAL_COLLECTIONS(tb.begin(), tb.end(), b.begin(), b.end());

  unsigned char uc = rw;
  BOOST_REQUIRE_EQUAL( uc, 1);

  signed char sc = rw;
  BOOST_REQUIRE_EQUAL( sc, 1);


  dynamic_bitset<> bs = rw;
  BOOST_REQUIRE_EQUAL(bs, dynamic_bitset<>(8, 1u));
}

void check_conversion_128_in_8bit( result_wrapper const & rw)
{
  std::string s = rw;
  BOOST_REQUIRE_EQUAL( s, "10000000" );

  vector<bool> a, b(8, false);
  b[7] = true;
  a = rw;
  BOOST_REQUIRE_EQUAL_COLLECTIONS(a.begin(), a.end(), b.begin(), b.end());

  vector<tribool> tb = rw;
  BOOST_REQUIRE_EQUAL_COLLECTIONS(tb.begin(), tb.end(), b.begin(), b.end());

  unsigned char uc = rw;
  BOOST_REQUIRE_EQUAL( uc, 128u);

  signed char sc = rw;
  BOOST_REQUIRE_EQUAL( sc, -128);

  int i = rw;
  BOOST_REQUIRE_EQUAL( i, -128);

  unsigned u = rw;
  BOOST_REQUIRE_EQUAL( u, 128u);

  dynamic_bitset<> bs = rw;
  BOOST_REQUIRE_EQUAL(bs, dynamic_bitset<>(8, 128u));

}

void check_conversion_13_in_8bit( result_wrapper const & rw)
{
  std::string s = rw;
  BOOST_REQUIRE_EQUAL( s, "00001101" );

  vector<bool> a, b(8, false);
  b[0] = true;
  b[2] = true;
  b[3] = true;
  a = rw;
  BOOST_REQUIRE_EQUAL_COLLECTIONS(a.begin(), a.end(), b.begin(), b.end());

  vector<tribool> tb = rw;
  BOOST_REQUIRE_EQUAL_COLLECTIONS(tb.begin(), tb.end(), b.begin(), b.end());

  unsigned char uc = rw;
  BOOST_REQUIRE_EQUAL( uc, 13u);

  signed char sc = rw;
  BOOST_REQUIRE_EQUAL( sc, 13);

  int i = rw;
  BOOST_REQUIRE_EQUAL( i, 13);

  unsigned u = rw;
  BOOST_REQUIRE_EQUAL( u, 13u);

  dynamic_bitset<> bs = rw;
  BOOST_REQUIRE_EQUAL(bs, dynamic_bitset<>(8, 13u));

}

BOOST_FIXTURE_TEST_SUITE(test_result_wrapper, Fixture )

BOOST_AUTO_TEST_CASE( from_string )
{
  const std::string val = "1101";
	result_wrapper rw(val);

  string s = rw;
  BOOST_REQUIRE_EQUAL(s, val);

  unsigned u = rw;
  BOOST_REQUIRE_EQUAL(u, 13);

  signed int i = rw;
  BOOST_REQUIRE_EQUAL(i, -3);

  check_conversion_1_in_8bit( result_wrapper( std::string("00000001")) );
  check_conversion_128_in_8bit( result_wrapper( std::string("10000000")) );
  check_conversion_13_in_8bit( result_wrapper( std::string("00001101")) );
}

BOOST_AUTO_TEST_CASE( bool_from_bool )
{
  bool b;
  b = result_wrapper(true);
  BOOST_REQUIRE_EQUAL(b, true);

  b = result_wrapper(false);
  BOOST_REQUIRE_EQUAL(b, false);
}

BOOST_AUTO_TEST_CASE( bool_from_string )
{
  bool b;
	result_wrapper rw1("1");
  b = rw1;
  BOOST_REQUIRE_EQUAL(b, true);

	result_wrapper rw2("0");
  b = rw2;
  BOOST_REQUIRE_EQUAL(b, false);
}

BOOST_AUTO_TEST_CASE( tribool_from_string )
{
  boost::logic::tribool t;
  t = result_wrapper ("1");
  BOOST_REQUIRE_EQUAL(t, true);

  t = result_wrapper ("0");
  BOOST_REQUIRE_EQUAL(t, false);

	t = result_wrapper ("X");
  BOOST_REQUIRE(boost::logic::indeterminate(t));
	t = result_wrapper ("x");
  BOOST_REQUIRE(boost::logic::indeterminate(t));
}

BOOST_AUTO_TEST_CASE( tribool_from_char )
{
  boost::logic::tribool t;
  t = result_wrapper ('1');
  BOOST_REQUIRE_EQUAL(t, true);

  t = result_wrapper ('0');
  BOOST_REQUIRE_EQUAL(t, false);

	t = result_wrapper ('X');
  BOOST_REQUIRE(boost::logic::indeterminate(t));
	t = result_wrapper ('x');
  BOOST_REQUIRE(boost::logic::indeterminate(t));
}

BOOST_AUTO_TEST_CASE( minus_one_from_string4 )
{
  const std::string val = "1111";
	result_wrapper rw(val);

  int i = rw;
  BOOST_REQUIRE_EQUAL(i, -1);
}

BOOST_AUTO_TEST_CASE( minus_one_from_string8 )
{
  const std::string val = "11111111";
	result_wrapper rw(val);

  signed char i = rw;
  BOOST_REQUIRE_EQUAL(static_cast<int>(i), -1);
}

BOOST_AUTO_TEST_CASE( minus_one_from_string32 )
{
  const std::string val = "11111111111111111111111111111111";
	result_wrapper rw(val);

  int32_t i = rw;
  BOOST_REQUIRE_EQUAL(i, -1);
}

BOOST_AUTO_TEST_CASE( from_dynamic_bitset )
{
	boost::dynamic_bitset<> bs(8, 255);
	result_wrapper rw(bs);

  unsigned i = rw;
  BOOST_REQUIRE_EQUAL(i, 255);

  check_conversion_1_in_8bit( result_wrapper(dynamic_bitset<>(8, 1)) );
  check_conversion_128_in_8bit( result_wrapper(dynamic_bitset<>(8, 128)) );
}

BOOST_AUTO_TEST_CASE( minus_one_from_dynamic_bitset )
{
	boost::dynamic_bitset<> bs(8, -1);
	result_wrapper rw(bs);

  int32_t i = rw;
  BOOST_REQUIRE_EQUAL(i, -1);
}

BOOST_AUTO_TEST_CASE( negative_from_dynamic_bitset )
{
	boost::dynamic_bitset<> bs(8, -65);
	result_wrapper rw(bs);

  int32_t i = rw;
  BOOST_REQUIRE_EQUAL(i, -65);
}

BOOST_AUTO_TEST_CASE( from_vector_bool )
{
  // check for 1
  std::vector< bool > vec (8, false);
  vec[0] = true;

  check_conversion_1_in_8bit( result_wrapper(vec) );

  // check  for 8u/-8
  vec[0]=false;
  vec[7]=true;
  check_conversion_128_in_8bit( result_wrapper(vec) );

  // check for 13 in 8bit
  vec[0]=true;
  vec[2]=true;
  vec[3]=true;
  vec[7]=false;
  check_conversion_13_in_8bit( result_wrapper(vec) );
}

BOOST_AUTO_TEST_CASE( from_vector_tribool )
{
  using boost::logic::indeterminate;

  // check for 1
  std::vector< boost::logic::tribool > vec (8, false);
  vec[0] = true;

  check_conversion_1_in_8bit( result_wrapper(vec) );

  // check  for 8u/-8
  vec[0]=false;
  vec[7]=true;
  check_conversion_128_in_8bit( result_wrapper(vec) );
  
  // check for 13 in 8bit
  vec[0]=true;
  vec[2]=true;
  vec[3]=true;
  vec[7]=false;
  check_conversion_13_in_8bit( result_wrapper(vec) );
}

BOOST_AUTO_TEST_CASE( from_integra_value_width )
{
  using boost::logic::indeterminate;

  // check for 1
  check_conversion_1_in_8bit( result_wrapper(1, 8) );

  // check  for 8u/-8
  check_conversion_128_in_8bit( result_wrapper(128, 8) );

  // check  for 8u/-8
  check_conversion_13_in_8bit( result_wrapper(13, 8) );
}

BOOST_AUTO_TEST_SUITE_END() // result_wrapper

//  vim: ft=cpp:ts=2:sw=2:expandtab
