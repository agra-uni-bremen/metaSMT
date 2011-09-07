#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/types/TypedSymbol.hpp>
#include <metaSMT/API/SymbolTable.hpp>
#include <boost/test/unit_test.hpp>
#include <string>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::logic;
using namespace metaSMT::logic::QF_BV;
using namespace metaSMT::type;
namespace proto = boost::proto;

BOOST_FIXTURE_TEST_SUITE(Types, Solver_Fixture )

BOOST_AUTO_TEST_CASE( init_typed_symbol ) {
  unsigned char const w = 32;

  TypedSymbol<ContextType> p(new_variable());
  TypedSymbol<ContextType> bv(new_bitvector(w), w);

  ContextType::result_type r = bv.eval(ctx);
  TypedSymbol<ContextType> expr(r, type::BitVector(w));

  BOOST_REQUIRE(  p.isBool() );
  BOOST_REQUIRE( !p.isBitVector() );
  BOOST_REQUIRE(  p.isPrimitiveBool() );
  BOOST_REQUIRE( !p.isPrimitiveBitVector() );
  BOOST_REQUIRE(  p.isPrimitive() );
  BOOST_REQUIRE( !p.isExpression() );

  BOOST_REQUIRE( !bv.isBool() );
  BOOST_REQUIRE(  bv.isBitVector() );
  BOOST_REQUIRE( !bv.isPrimitiveBool() );
  BOOST_REQUIRE(  bv.isPrimitiveBitVector() );
  BOOST_REQUIRE(  bv.isPrimitive() );
  BOOST_REQUIRE( !bv.isExpression() );

  BOOST_REQUIRE( !expr.isBool() );
  BOOST_REQUIRE(  expr.isBitVector() );
  BOOST_REQUIRE( !expr.isPrimitiveBool() );
  BOOST_REQUIRE( !expr.isPrimitiveBitVector() );
  BOOST_REQUIRE( !expr.isPrimitive() );
  BOOST_REQUIRE(  expr.isExpression() );
}

BOOST_AUTO_TEST_CASE( check_bitwidth ) {
  unsigned char const w = 32;

  TypedSymbol<ContextType> bv(new_bitvector(w), w);
  BOOST_REQUIRE( w == boost::get<type::BitVector>(bv.type).width );

  ContextType::result_type r = bv.eval(ctx);
  TypedSymbol<ContextType> expr(r, type::BitVector(w));
  BOOST_REQUIRE( expr.isBitVector() );
  BOOST_REQUIRE( expr.isExpression() );
  BOOST_REQUIRE( !expr.isPrimitive() );
  BOOST_REQUIRE( w == boost::get<type::BitVector>(expr.type).width );

  type::BitVector bv_type = expr.getType(type::BitVector());
  BOOST_REQUIRE( w == bv_type.width );
}

BOOST_AUTO_TEST_CASE( get_id ) {
  unsigned char const w = 32;

  predicate p_primitive = new_variable();
  bitvector bv_primitive = new_bitvector(w);

  TypedSymbol<ContextType> p(p_primitive);
  TypedSymbol<ContextType> bv(bv_primitive, w);

  ContextType::result_type r = bv.eval(ctx);
  TypedSymbol<ContextType> expr(r, type::BitVector(w));

  BOOST_REQUIRE( p.isPrimitiveBool() );
  if ( p.isPrimitiveBool() ) {
    predicate p_val = boost::get<predicate>(p.value);
    BOOST_REQUIRE( boost::proto::value( p_val ).id == boost::proto::value( p_primitive ).id );
  }

  BOOST_REQUIRE( bv.isPrimitiveBitVector() );
  if ( bv.isPrimitiveBitVector() ) {
    bitvector bv_val = boost::get<bitvector>(bv.value);
    BOOST_REQUIRE( boost::proto::value( bv_val ).id == boost::proto::value( bv_primitive ).id );
  }
}

BOOST_AUTO_TEST_CASE( conversion ) {
  unsigned char const w = 32;

  predicate p_primitive = new_variable();
  bitvector bv_primitive = new_bitvector(w);

  TypedSymbol<ContextType> p(p_primitive);
  TypedSymbol<ContextType> bv(bv_primitive, w);

  assertion(ctx, equal(type::detail::to_bool(ctx, bv), p_primitive));
  assertion(ctx, equal(zero_extend(31, type::detail::to_bitvector(ctx, p)), bv_primitive));
  
  assertion(ctx, equal(bv.toBool(ctx), p_primitive));
  assertion(ctx, equal(p.toBV(ctx, w), bv_primitive));

  solve( ctx );
}

BOOST_AUTO_TEST_SUITE_END() // Types

//  vim: ft=cpp:ts=2:sw=2:expandtab
