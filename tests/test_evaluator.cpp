#include <metaSMT/support/disable_warnings.hpp>
#include <boost/test/unit_test.hpp>
#include <metaSMT/support/enable_warnings.hpp>
#include <metaSMT/frontend/Logic.hpp>
#include <metaSMT/API/Assumption.hpp>
#include <metaSMT/API/Evaluator.hpp>

using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::logic;

namespace metaSMT {
  template <>
  struct Evaluator<char> : public boost::mpl::true_ {
    template < typename Context >
    static typename Context::result_type eval(Context &ctx, char const &c) {
      // assert( (c == '1' || c == '0' || c == 'X' || c == 'x') &&
      //         "has to be 0, 1, X, or x character" );

      if ( c == '1' ) {
        return evaluate(ctx, True);
      }
      else if ( c == '0' ) {
        return evaluate(ctx, False);
      }
      else if ( c == 'X' || c == 'x' ) {
        // prefer false in case of a don't care
        return evaluate(ctx, False);
      }

      // error
      std::string message = "trying evaluate an unsupported character: ";
      message += c;
      throw std::runtime_error(message);
    }
  }; // Evaluator
} // metaSMT

BOOST_FIXTURE_TEST_SUITE(eval, Solver_Fixture )

BOOST_AUTO_TEST_CASE( char_evaluator )
{
  predicate x = new_variable();
  assertion(ctx, logic::equal(x, x));
  BOOST_REQUIRE( solve(ctx) );

  bool xd;
  assumption(ctx, logic::equal(x, '1'));
  BOOST_REQUIRE( solve(ctx) );
  xd = read_value(ctx, x);
  BOOST_CHECK_EQUAL(xd, true);

  assumption(ctx, logic::equal(x, '0'));
  BOOST_REQUIRE( solve(ctx) );
  xd = read_value(ctx, x);
  BOOST_CHECK_EQUAL(xd, false);

  assumption(ctx, logic::equal(x, 'X'));
  BOOST_REQUIRE( solve(ctx) );
  xd = read_value(ctx, x);
  BOOST_CHECK_EQUAL(xd, false);

  BOOST_CHECK_THROW(
    assertion(ctx, logic::equal(x, 'U'))
  , std::runtime_error
  );
}

BOOST_AUTO_TEST_SUITE_END() // eval

//  vim: ft=cpp:ts=2:sw=2:expandtab
