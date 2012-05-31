#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/API/Comment.hpp>
#include <metaSMT/API/SymbolTable.hpp>
#include <metaSMT/API/Stack.hpp>
#include <boost/test/unit_test.hpp>

// lazy headers

using namespace metaSMT;
using namespace logic;
using namespace logic::QF_BV;
namespace proto = boost::proto;

BOOST_FIXTURE_TEST_SUITE(annotate_t, Solver_Fixture )

struct Lookup {
  std::map<unsigned, std::string> map_;

  std::string operator()(unsigned id) {
    return map_[id];
  }

  void insert(predicate p, std::string const &name) {
    map_.insert(std::make_pair(boost::proto::value(p).id, name));
  }
};

BOOST_AUTO_TEST_CASE( comment_t )
{
  predicate x = new_variable();
  assertion( ctx, True);
  comment( ctx, "an assertion");
  assertion( ctx, x);
  comment( ctx, "an assertion with a comment string\n"
                "which uses more than one line" );
  assertion( ctx, x);
  comment( ctx, "finally call solve");
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( stacked_comments ) {
  predicate x = new_variable();
  comment( ctx, "before push" );
  push( ctx );
  comment( ctx, "after push" );
  assertion ( ctx, False );
  BOOST_REQUIRE ( !solve(ctx) );
  BOOST_REQUIRE ( !solve(ctx) );
  comment( ctx, "before pop" );
  pop( ctx );
  comment( ctx, "after pop" );
  BOOST_REQUIRE ( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( symbol_table )
{
  Lookup lookup;
  predicate x = new_variable();
  lookup.insert(x, "x");
  set_symbol_table( ctx, lookup);
  assertion( ctx, x);
  BOOST_REQUIRE( solve(ctx) );
}

BOOST_AUTO_TEST_CASE( read_value_t )
{
  Lookup lookup;
  unsigned const w = 17;
  predicate x[w];
  for ( unsigned u = 0; u < w; ++u ) {
    x[u] = new_variable();
  }

  // weird (but syntactically legal) names with respect to SMT-LIB 2
  // taken from the SMT-LIB 2 standard document
  lookup.insert(x[0], "+");
  lookup.insert(x[1], "<=");
  lookup.insert(x[2], "x");
  lookup.insert(x[3], "plus");
  lookup.insert(x[4], "**");
  lookup.insert(x[5], "$");
  lookup.insert(x[6], "<sas");
  lookup.insert(x[7], "<adf>");
  lookup.insert(x[8], "abc77");
  lookup.insert(x[9], "*$s&6");
  lookup.insert(x[10], ".kkk");
  lookup.insert(x[11], ".8");
  lookup.insert(x[12], "+34");
  lookup.insert(x[13], "-32");
  lookup.insert(x[14], "|this is a single quoted symbol|");
  lookup.insert(x[15], "||");
  lookup.insert(x[16], "| af klj ^ * ( 0 asfsfe2(&*)&(#^$ > > >?\" \']]984|");
  set_symbol_table( ctx, lookup);

  BOOST_REQUIRE( solve(ctx) );
  bool xd;
  for ( unsigned u = 0; u < w; ++u ) {
    assumption( ctx, equal(x[u], True) );
    BOOST_REQUIRE( solve(ctx) );
    xd = read_value(ctx, x[u]);
    BOOST_REQUIRE_EQUAL( xd, true );

    assumption( ctx, equal(x[u], False) );
    BOOST_REQUIRE( solve(ctx) );
    xd = read_value(ctx, x[u]);
    BOOST_REQUIRE_EQUAL( xd, false );
  }
}

BOOST_AUTO_TEST_SUITE_END() //lazy_t

//  vim: ft=cpp:ts=2:sw=2:expandtab

