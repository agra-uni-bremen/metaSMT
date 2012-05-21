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
  BOOST_REQUIRE( !p.isArray() );
  BOOST_REQUIRE(  p.isPrimitiveBool() );
  BOOST_REQUIRE( !p.isPrimitiveBitVector() );
  BOOST_REQUIRE( !p.isPrimitiveArray() );
  BOOST_REQUIRE(  p.isPrimitive() );
  BOOST_REQUIRE( !p.isExpression() );

  BOOST_REQUIRE( !bv.isBool() );
  BOOST_REQUIRE(  bv.isBitVector() );
  BOOST_REQUIRE( !bv.isArray() );
  BOOST_REQUIRE( !bv.isPrimitiveBool() );
  BOOST_REQUIRE(  bv.isPrimitiveBitVector() );
  BOOST_REQUIRE( !bv.isPrimitiveArray() );
  BOOST_REQUIRE(  bv.isPrimitive() );
  BOOST_REQUIRE( !bv.isExpression() );

  BOOST_REQUIRE( !expr.isBool() );
  BOOST_REQUIRE(  expr.isBitVector() );
  BOOST_REQUIRE( !expr.isPrimitiveBool() );
  BOOST_REQUIRE( !expr.isPrimitiveBitVector() );
  BOOST_REQUIRE( !expr.isPrimitiveArray() );
  BOOST_REQUIRE( !expr.isPrimitive() );
  BOOST_REQUIRE(  expr.isExpression() );
}

BOOST_AUTO_TEST_CASE( init_typed_array_symbol ) {
  unsigned char const elem_width = 8;
  unsigned char const index_width = 4;

  TypedSymbol<ContextType> a1(new_array(elem_width, index_width),
                              elem_width, index_width);
  BOOST_REQUIRE( !a1.isBool() );
  BOOST_REQUIRE( !a1.isBitVector() );
  BOOST_REQUIRE(  a1.isArray() );
  BOOST_REQUIRE( !a1.isPrimitiveBool() );
  BOOST_REQUIRE( !a1.isPrimitiveBitVector() );
  BOOST_REQUIRE(  a1.isPrimitiveArray() );
  BOOST_REQUIRE( !a1.isExpression() );

  ContextType::result_type r = evaluate(ctx, new_array(elem_width, index_width));
  TypedSymbol<ContextType> a2(r, type::Array(elem_width, index_width));
  BOOST_REQUIRE( !a2.isBool() );
  BOOST_REQUIRE( !a2.isBitVector() );
  BOOST_REQUIRE(  a2.isArray() );
  BOOST_REQUIRE( !a2.isPrimitiveBool() );
  BOOST_REQUIRE( !a2.isPrimitiveBitVector() );
  BOOST_REQUIRE( !a2.isPrimitiveArray() );
  BOOST_REQUIRE(  a2.isExpression() );
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

BOOST_AUTO_TEST_CASE( check_array_widths ) {
  unsigned char const elem_width = 8;
  unsigned char const index_width = 4;

  TypedSymbol<ContextType> a(new_array(elem_width, index_width),
                             elem_width, index_width);
  BOOST_REQUIRE( elem_width == boost::get<type::Array>(a.type).elem_width );
  BOOST_REQUIRE( index_width == boost::get<type::Array>(a.type).index_width );

  ContextType::result_type r = a.eval(ctx);
  TypedSymbol<ContextType> expr(r, type::Array(elem_width, index_width));
  BOOST_REQUIRE( expr.isArray() );
  BOOST_REQUIRE( expr.isExpression() );
  BOOST_REQUIRE( !expr.isPrimitive() );
  BOOST_REQUIRE( elem_width == boost::get<type::Array>(expr.type).elem_width );
  BOOST_REQUIRE( index_width == boost::get<type::Array>(expr.type).index_width );

  type::Array array_type = expr.getType(type::Array());
  BOOST_REQUIRE( elem_width == array_type.elem_width );
  BOOST_REQUIRE( index_width == array_type.index_width );
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

BOOST_AUTO_TEST_CASE( get_array_id ) {
  unsigned char const elem_width = 8;
  unsigned char const index_width = 4;

  array a_primitive = new_array(elem_width, index_width);

  TypedSymbol<ContextType> a(a_primitive, elem_width, index_width);

  ContextType::result_type r = a.eval(ctx);
  TypedSymbol<ContextType> expr(r, type::Array(elem_width, index_width));

  BOOST_REQUIRE( a.isPrimitiveArray() );
  if ( a.isPrimitiveArray() ) {
    array a_val = boost::get<array>(a.value);
    BOOST_REQUIRE( boost::proto::value( a_val ).id == boost::proto::value( a_primitive ).id );
  }
}

BOOST_AUTO_TEST_CASE( conversion ) {
  unsigned char const w = 32;

  predicate p_primitive = new_variable();
  bitvector bv_primitive = new_bitvector(w);

  TypedSymbol<ContextType> p(p_primitive);
  TypedSymbol<ContextType> bv(bv_primitive, w);

  metaSMT::assertion(ctx, logic::equal(type::detail::to_bool(ctx, bv), p_primitive));
  metaSMT::assertion(ctx, logic::equal(zero_extend(w-1, type::detail::to_bitvector(ctx, p)), bv_primitive));

  metaSMT::assertion(ctx, logic::equal(bv.toBool(ctx), p_primitive));
  metaSMT::assertion(ctx, logic::equal(p.toBV(ctx, w), bv_primitive));

  solve( ctx );
}

BOOST_AUTO_TEST_CASE( array_conversion ) {
  unsigned char const elem_width = 8;
  unsigned char const index_width = 2;
  array a_primitive = new_array(elem_width, index_width);
  TypedSymbol<ContextType> a(a_primitive, elem_width, index_width);

  predicate p = new_variable();
  metaSMT::assertion(ctx, logic::equal(p, a.toBool(ctx)));
  BOOST_REQUIRE( solve( ctx ) );

  bitvector bv1 = new_bitvector(elem_width*(1 << index_width));
  metaSMT::assertion(ctx, logic::equal(bv1, a.toBV(ctx)));
  BOOST_REQUIRE( solve( ctx ) );

  unsigned char const offsett = 32;
  unsigned char const ext_size = (1 << index_width)*elem_width+offsett;
  bitvector bv2 = new_bitvector(ext_size);
  metaSMT::assertion(ctx, logic::equal(bv2, a.toBV(ctx, ext_size)));

  BOOST_REQUIRE( solve( ctx ) );
}

BOOST_AUTO_TEST_SUITE_END() // Types

//  vim: ft=cpp:ts=2:sw=2:expandtab
