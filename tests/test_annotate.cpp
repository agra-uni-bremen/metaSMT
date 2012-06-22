#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/Comment.hpp>
#include <boost/test/unit_test.hpp>

// lazy headers

using namespace metaSMT;
using namespace logic;
using namespace logic::QF_BV;
namespace proto = boost::proto;


BOOST_FIXTURE_TEST_SUITE(annotate_t, Solver_Fixture )

BOOST_AUTO_TEST_CASE( comment1 )
{
  predicate x = new_variable();
  assertion( ctx, True);
  comment( ctx, "jetzt kommt eine variable");
  assertion( ctx, x);
  comment( ctx, "jetzt kommt solve");
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_SUITE_END() //lazy_t

//  vim: ft=cpp:ts=2:sw=2:expandtab

