#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/API/Comment.hpp>
#include <metaSMT/API/SymbolTable.hpp>
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

BOOST_AUTO_TEST_CASE( comment1 )
{
  predicate x = new_variable();
  assertion( ctx, True);
  comment( ctx, "jetzt kommt eine variable");
  assertion( ctx, x);
  comment( ctx, "jetzt kommt solve");
  BOOST_REQUIRE( solve(ctx) );
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

BOOST_AUTO_TEST_SUITE_END() //lazy_t

//  vim: ft=cpp:ts=2:sw=2:expandtab

