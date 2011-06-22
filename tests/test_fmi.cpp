#include <metaSMT/frontend/fmi.hpp>
#include <metaSMT/frontend/QF_BV.hpp>
#include <boost/proto/debug.hpp>
#include <boost/test/unit_test.hpp>
#include <string>

using namespace metaSMT;
using boost::proto::display_expr;

BOOST_FIXTURE_TEST_SUITE(fmi_t, Solver_Fixture )

BOOST_AUTO_TEST_CASE( syntax )
{
  fmi::Solver solver;
  unsigned lines=0, pos=0; 
  fmi::bv control = fmi::new_variable(solver, 3);
  std::vector<fmi::bv> nextGate, currentGate;
  nextGate.push_back( fmi::new_variable(solver, 1) );
  currentGate.push_back( fmi::new_variable(solver, 1) );
  fmi::bv target;
  using fmi::_0;
  using fmi::_1;
  using fmi::_2;
  using fmi::_3;

  //nextGate [ pos ] = fmi::new_variable (solver, lines);
  fmi::bv hit      = fmi::new_variable (solver, 1);

  //proto::display_expr(fmi::generate(_0 == _0));

  using namespace logic::QF_BV;

  fmi::generate (solver
    , _0 %= (_1 & _2 & _3) == _2
    , hit
    , currentGate [ pos ]
    , control // to many arguments
  );

  fmi::generate (solver
      , _0 %= (_1 & _2) == _2
      , hit, currentGate [ pos ] , control );

  fmi::bv zext = fmi::zero_extend (solver, hit, lines-1);

  display_expr( transform::fmiToQF_BV()(
      _0 %= _1 ^ (_2 << _3)
      ));

  fmi::generate (solver,
      _0 %= _1 ^ (_2 & _3),
      nextGate [ pos ], currentGate [ pos  ], zext, target);  


  fmi::generate ( solver, hit == ( (currentGate[pos] & control) == control) );
}

BOOST_AUTO_TEST_CASE( simple_sat )
{
  fmi::bv control = fmi::new_variable(ctx, 3);

  fmi::assertion ( ctx, control == control  );

  BOOST_REQUIRE( solve( ctx ) );

  fmi::assertion ( ctx, control != control  );

  BOOST_REQUIRE( !solve( ctx ) );
}

BOOST_AUTO_TEST_SUITE_END() //QF_BV

//  vim: ft=cpp:ts=2:sw=2:expandtab
