#include <metaSMT/API/AssignRandomBits.hpp>
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

BOOST_FIXTURE_TEST_SUITE(assign_random_bits_t, Solver_Fixture )

BOOST_AUTO_TEST_CASE( test_random_bits )
{
  bitvector x = new_bitvector(32);
  bitvector y = new_bitvector(32);
  bitvector z = new_bitvector(32);
  
  std::vector<bitvector> variables;
  variables.push_back(x);
  variables.push_back(y);
  variables.push_back(z);

  unsigned x1, y1, z1;
  unsigned x2, y2, z2;

 
  BOOST_REQUIRE( solve(ctx) );
  assign_random_bits(ctx, variables);
 
  x1 = read_value(ctx,x);
  y1 = read_value(ctx,y);
  z1 = read_value(ctx,z);

  BOOST_REQUIRE ( solve(ctx) );
  assign_random_bits(ctx, variables);

  x2 = read_value(ctx,x);
  y2 = read_value(ctx,y);
  z2 = read_value(ctx,z);

  BOOST_REQUIRE ( solve(ctx) );

  BOOST_REQUIRE ( x1 != x2 || y1 != y2 || z1 != z2 ); 

}

BOOST_AUTO_TEST_CASE( test_solve_random )
{
  bitvector x = new_bitvector(32);
  bitvector y = new_bitvector(32);
  bitvector z = new_bitvector(32);
  
  std::vector<bitvector> variables;
  variables.push_back(x);
  variables.push_back(y);
  variables.push_back(z);

  unsigned x1, y1, z1;
  unsigned x2, y2, z2;
 
  BOOST_REQUIRE( solve_with_random_bits(ctx, variables) );
 
  x1 = read_value(ctx,x);
  y1 = read_value(ctx,y);
  z1 = read_value(ctx,z);

  BOOST_REQUIRE ( solve_with_random_bits(ctx,variables) );
  x2 = read_value(ctx,x);
  y2 = read_value(ctx,y);
  z2 = read_value(ctx,z);

  BOOST_REQUIRE ( solve_with_random_bits(ctx,variables) );

  BOOST_REQUIRE ( x1 != x2 || y1 != y2 || z1 != z2 ); 

}

BOOST_AUTO_TEST_SUITE_END() //Solver

//  vim: ft=cpp:ts=2:sw=2:expandtab
