#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/support/lazy.hpp>

#include <metaSMT/support/disable_warnings.hpp>
#include <boost/test/unit_test.hpp>
#include <metaSMT/support/enable_warnings.hpp>

#include <numeric>

// lazy headers

using namespace metaSMT;
using namespace logic;
using namespace logic::QF_BV;
namespace proto = boost::proto;


BOOST_FIXTURE_TEST_SUITE(lazy_t, Solver_Fixture )

BOOST_AUTO_TEST_CASE( andiN )
{
  typedef ContextType::result_type result_type;

  boost::function< result_type ( predicate const &, predicate const & ) > 
    lazy_andiN = metaSMT::lazy( ctx, And( arg1, Not(arg2)) ) ;

  predicate x = new_variable();
  predicate y = new_variable();

  assumption( ctx, metaSMT::logic::equal(And(x, Not(y)), lazy_andiN(x,y)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption( ctx, nequal(And(x, Not(y)), lazy_andiN(x,y)) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( lazy_result_type )
{
  typedef ContextType::result_type result_type;

  boost::function< result_type ( predicate const &, result_type const & ) > 
    lazy_Xor = metaSMT::lazy( ctx, Xor( arg1, arg2) ) ;

  predicate x = new_variable();
  result_type y = evaluate(ctx, new_variable());

  assumption(ctx, metaSMT::logic::equal( Xor(x,y), lazy_Xor(x,y)) );
  BOOST_REQUIRE( solve(ctx) );

  assumption(ctx, nequal( Xor(x,y), lazy_Xor(x,y)) );
  BOOST_REQUIRE( !solve(ctx) );
}

BOOST_AUTO_TEST_CASE( lazy_accumulate )
{
  unsigned count = 100;
  std::vector< predicate > preds;
  for (unsigned i = 0; i < count; ++i) {
    preds.push_back( new_variable() );
  }

  ContextType::result_type initial = evaluate(ctx, False);

  metaSMT::assertion( ctx, std::accumulate(preds.begin(), preds.end(), initial,
        metaSMT::lazy(ctx, Xor(arg1, arg2) )
  ));
  
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_SUITE_END() //lazy_t

//  vim: ft=cpp:ts=2:sw=2:expandtab

