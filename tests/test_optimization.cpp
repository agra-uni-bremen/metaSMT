#include <boost/test/unit_test.hpp>
#include <metaSMT/support/optimization.hpp>
#include <metaSMT/frontend/Logic.hpp>
#include <boost/assign/std/vector.hpp>
#include <vector>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::logic;
using namespace metaSMT::cardinality;
using namespace boost::assign;
namespace proto = boost::proto;

BOOST_FIXTURE_TEST_SUITE(optimization_t, Solver_Fixture )

template < typename Context >
void minimize_all( std::string const optimize_with, std::string const constrain_with,
                   Context &ctx, unsigned ub ) {
  set_option( ctx, "cardinality", optimize_with );
  for (unsigned num_vars = 1; num_vars <= ub; ++num_vars) {
    std::vector< logic::predicate > p;
    for ( unsigned u = 0; u < num_vars; ++u ) {
      p.push_back( logic::new_variable() );
    }

    for ( unsigned value = 1; value <= num_vars; ++value ) {
      std::cerr << "#VAR = " << num_vars << " MIN = " << value << '\n';
      push(ctx);
      metaSMT::assertion( ctx, evaluate(ctx,
        cardinality::cardinality(cardinality::tag::geq_tag(), p, value, constrain_with))
      );
      unsigned const min = optimization::minimize(ctx, p);
      BOOST_REQUIRE_EQUAL( min, value );
      pop(ctx);
    }
  }
}

BOOST_AUTO_TEST_CASE( min10_bdd1 ) { minimize_all( "bdd", "bdd",   ctx,  10); }
BOOST_AUTO_TEST_CASE( min20_bdd1 ) { minimize_all( "bdd", "bdd",   ctx,  20); }
BOOST_AUTO_TEST_CASE( min10_bdd2 ) { minimize_all( "bdd", "adder", ctx,  10); }
BOOST_AUTO_TEST_CASE( min20_bdd2 ) { minimize_all( "bdd", "adder", ctx,  20); }

BOOST_AUTO_TEST_CASE( min10_adder1 ) { minimize_all( "adder", "bdd",   ctx,  10); }
BOOST_AUTO_TEST_CASE( min20_adder1 ) { minimize_all( "adder", "bdd",   ctx,  20); }
BOOST_AUTO_TEST_CASE( min10_adder2 ) { minimize_all( "adder", "adder", ctx,  10); }
BOOST_AUTO_TEST_CASE( min20_adder2 ) { minimize_all( "adder", "adder", ctx,  20); }

template < typename Context >
void maximize_all( std::string const optimize_with, std::string const constrain_with,
                   Context &ctx, unsigned ub ) {
  set_option( ctx, "cardinality", optimize_with );
  for (unsigned num_vars = 1; num_vars <= ub; ++num_vars) {
    std::vector< logic::predicate > p;
    for ( unsigned u = 0; u < num_vars; ++u ) {
      p.push_back( logic::new_variable() );
    }

    for ( unsigned value = 1; value <= num_vars; ++value ) {
      std::cerr << "#VAR = " << num_vars << " MAX = " << value << '\n';
      push(ctx);
      metaSMT::assertion( ctx, evaluate(ctx,
        cardinality::cardinality(cardinality::tag::leq_tag(), p, value, constrain_with))
      );
      unsigned const max = optimization::maximize(ctx, p);
      BOOST_CHECK_EQUAL( max, value );
      pop(ctx);
    }
  }
}

BOOST_AUTO_TEST_CASE( max10_bdd1 ) { maximize_all( "bdd", "bdd",   ctx,  10); }
BOOST_AUTO_TEST_CASE( max20_bdd1 ) { maximize_all( "bdd", "bdd",   ctx,  20); }
BOOST_AUTO_TEST_CASE( max10_bdd2 ) { maximize_all( "bdd", "adder", ctx,  10); }
BOOST_AUTO_TEST_CASE( max20_bdd2 ) { maximize_all( "bdd", "adder", ctx,  20); }

BOOST_AUTO_TEST_CASE( max10_adder1 ) { maximize_all( "adder", "bdd",   ctx,  10); }
BOOST_AUTO_TEST_CASE( max20_adder1 ) { maximize_all( "adder", "bdd",   ctx,  20); }
BOOST_AUTO_TEST_CASE( max10_adder2 ) { maximize_all( "adder", "adder", ctx,  10); }
BOOST_AUTO_TEST_CASE( max20_adder2 ) { maximize_all( "adder", "adder", ctx,  20); }

BOOST_AUTO_TEST_SUITE_END()
