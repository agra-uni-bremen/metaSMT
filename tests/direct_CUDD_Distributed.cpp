#define BOOST_TEST_MODULE direct_CUDD_Distributed
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/BitBlast.hpp>
#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/backend/CUDD_Distributed.hpp>
#include <boost/random/uniform_int.hpp>
#include <boost/random/mersenne_twister.hpp>
#include <boost/test/floating_point_comparison.hpp>


using namespace metaSMT::solver;
using namespace metaSMT;

struct Solver_Fixture {
  Solver_Fixture() 
  : gen( time(NULL) )
  , rnd ( random_bit(gen) )
  {  }
  //typedef DirectSolver_Context< Group < CUDD_Distributed > > ContextType;
  typedef DirectSolver_Context< BitBlast<CUDD_Distributed > > ContextType;
  //typedef DirectSolver_Context< CUDD_Distributed > ContextType;
  ContextType ctx ;

  struct random_bit {
    random_bit( boost::mt19937 & gen ) : gen(gen), rnd(0, 1) {}
   
    bool operator() () {
      return rnd(gen);
    }
   
    boost::mt19937 & gen;
    boost::uniform_int<unsigned short> rnd;
  };

  boost::mt19937 gen;
  boost::function0<bool> rnd;

};

#include "test_solver.cpp"
#include "test_QF_BV.cpp"
// #include "test_Array.cpp"
//#include "test_group.cpp"
//#include "test_unsat.cpp"

static const unsigned repeat = 10000;
BOOST_FIXTURE_TEST_SUITE(dist, Solver_Fixture )

BOOST_AUTO_TEST_CASE( test1 )
{
   predicate x = new_variable();
   predicate y = new_variable();
   predicate z = new_variable();

   assumption( ctx, Ite(x, y, z));
   BOOST_CHECK( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( dist_Or )
{
  predicate x = new_variable();
  predicate y = new_variable();

  assertion( ctx, Or(x, y));

  std::map<unsigned, unsigned> counter;
  for(unsigned i = 0; i < repeat; ++i)
  {
    BOOST_REQUIRE( solve(ctx) );
    unsigned xv = read_value( ctx, x ).randX(rnd);
    unsigned yv = read_value( ctx, y ).randX(rnd);
    counter [xv+2*yv]++;
  }

  for(std::map<unsigned,unsigned>::iterator iter = counter.begin(); iter != counter.end(); ++iter)
  {
    std::cout << iter->first << " " << iter->second << std::endl; 
  }
  std::cout << std::endl; 
  double expected = repeat/3.0;
  double tolerance = 5;
  BOOST_CHECK_EQUAL( counter[0], 0u);
  BOOST_CHECK_CLOSE((double)counter[1],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[2],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[3],expected, tolerance);
}

BOOST_AUTO_TEST_CASE( dist_And )
{
  predicate x = new_variable();
  predicate y = new_variable();

  assertion( ctx, And(x, y));

  std::map<unsigned, unsigned> counter;
  for(unsigned i = 0; i < repeat; ++i)
  {
    BOOST_REQUIRE( solve(ctx) );
    unsigned xv = read_value( ctx, x ).randX(rnd);
    unsigned yv = read_value( ctx, y ).randX(rnd);
    counter [xv+2*yv]++;
  }

  for(std::map<unsigned,unsigned>::iterator iter = counter.begin(); iter != counter.end(); ++iter)
  {
    std::cout << iter->first << " " << iter->second << std::endl; 
  }
  std::cout << std::endl; 
  BOOST_CHECK_EQUAL( counter[0], 0u);
  BOOST_CHECK_EQUAL( counter[1], 0u);
  BOOST_CHECK_EQUAL( counter[2], 0u);
  BOOST_CHECK_EQUAL( counter[3], repeat);
}

BOOST_AUTO_TEST_CASE( dist_Xor)
{
  predicate x = new_variable();
  predicate y = new_variable();

  assertion( ctx, Xor(x, y));

  std::map<unsigned, unsigned> counter;
  for(unsigned i = 0; i < repeat; ++i)
  {
    BOOST_REQUIRE( solve(ctx) );
    unsigned xv = read_value( ctx, x ).randX(rnd);
    unsigned yv = read_value( ctx, y ).randX(rnd);
    counter [xv+2*yv]++;
  }

  for(std::map<unsigned,unsigned>::iterator iter = counter.begin(); iter != counter.end(); ++iter)
  {
    std::cout << iter->first << " " << iter->second << std::endl; 
  }
  std::cout << std::endl; 
  double expected = repeat/2.0;
  double tolerance = 5;
  BOOST_CHECK_EQUAL( counter[0], 0u);
  BOOST_CHECK_EQUAL( counter[3], 0u);
  BOOST_CHECK_CLOSE((double)counter[1],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[2],expected, tolerance);
}

BOOST_AUTO_TEST_CASE( dist_Nor )
{
  predicate x = new_variable();
  predicate y = new_variable();

  assertion( ctx, Nor(x, y));

  std::map<unsigned, unsigned> counter;
  for(unsigned i = 0; i < repeat; ++i)
  {
    BOOST_REQUIRE( solve(ctx) );
    unsigned xv = read_value( ctx, x ).randX(rnd);
    unsigned yv = read_value( ctx, y ).randX(rnd);
    counter [xv+2*yv]++;
  }

  for(std::map<unsigned,unsigned>::iterator iter = counter.begin(); iter != counter.end(); ++iter)
  {
    std::cout << iter->first << " " << iter->second << std::endl; 
  }
  std::cout << std::endl; 
  BOOST_CHECK_EQUAL(counter[1],0u);
  BOOST_CHECK_EQUAL(counter[2],0u);
  BOOST_CHECK_EQUAL(counter[3],0u);
  BOOST_CHECK_EQUAL(counter[0],repeat);
}

BOOST_AUTO_TEST_CASE( dist_Nand )
{
  predicate x = new_variable();
  predicate y = new_variable();

  assertion( ctx, Nand(x, y));

  std::map<unsigned, unsigned> counter;
  for(unsigned i = 0; i < repeat; ++i)
  {
    BOOST_REQUIRE( solve(ctx) );
    unsigned xv = read_value( ctx, x ).randX(rnd);
    unsigned yv = read_value( ctx, y ).randX(rnd);
    counter [xv+2*yv]++;
    //std::cout << read_value(ctx,x) << " " << read_value(ctx,y) << std::endl; 
  }

  for(std::map<unsigned,unsigned>::iterator iter = counter.begin(); iter != counter.end(); ++iter)
  {
    std::cout << iter->first << " " << iter->second << std::endl; 
  }
  std::cout << std::endl; 
  BOOST_CHECK_NE(counter[0],0u);
  BOOST_CHECK_NE(counter[1],0u);
  BOOST_CHECK_NE(counter[2],0u);
  BOOST_CHECK_EQUAL(counter[3],0u);
}

BOOST_AUTO_TEST_CASE( dist_Xnor )
{
  predicate x = new_variable();
  predicate y = new_variable();

  assertion( ctx, Xnor(x, y));

  std::map<unsigned, unsigned> counter;
  for(unsigned i = 0; i < repeat; ++i)
  {
    BOOST_REQUIRE( solve(ctx) );
    unsigned xv = read_value( ctx, x ).randX(rnd);
    unsigned yv = read_value( ctx, y ).randX(rnd);
    counter [xv+2*yv]++;
  }

  for(std::map<unsigned,unsigned>::iterator iter = counter.begin(); iter != counter.end(); ++iter)
  {
    std::cout << iter->first << " " << iter->second << std::endl; 
  }
  std::cout << std::endl; 
  double expected = repeat/2.0;
  double tolerance = 5;
  BOOST_CHECK_EQUAL( counter[1], 0u);
  BOOST_CHECK_EQUAL( counter[2], 0u);
  BOOST_CHECK_CLOSE((double)counter[0],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[3],expected, tolerance);

}

BOOST_AUTO_TEST_CASE( dist_aLT16 )
{
  using namespace metaSMT::logic::QF_BV;
  bitvector a = new_bitvector(8);

  assertion( ctx, bvult(a, bvuint(16,8)));

  std::map<unsigned, unsigned> counter;
  for(unsigned i = 0; i < repeat; ++i)
  {
    BOOST_REQUIRE( solve(ctx) );
    //std::cout << read_value( ctx, a ) << std::endl;
    unsigned av = read_value( ctx, a ).randX(rnd);
    counter [av]++;
  }

  for(std::map<unsigned,unsigned>::iterator iter = counter.begin(); iter != counter.end(); ++iter)
  {
    std::cout << iter->first << " " << iter->second << std::endl; 
  }
  std::cout << std::endl;
  double expected = repeat/16.0;
  double tolerance = 15;
  BOOST_CHECK_CLOSE((double)counter[0],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[1],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[2],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[3],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[4],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[5],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[6],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[7],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[8],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[9],expected, tolerance);
  BOOST_CHECK_CLOSE((double)counter[10],expected,tolerance);
  BOOST_CHECK_CLOSE((double)counter[11],expected,tolerance);
  BOOST_CHECK_CLOSE((double)counter[12],expected,tolerance);
  BOOST_CHECK_CLOSE((double)counter[13],expected,tolerance);
  BOOST_CHECK_CLOSE((double)counter[14],expected,tolerance);
  BOOST_CHECK_CLOSE((double)counter[15],expected,tolerance);
}


BOOST_AUTO_TEST_SUITE_END() //dist

// vim: ft=cpp:ts=2:sw=2:et
