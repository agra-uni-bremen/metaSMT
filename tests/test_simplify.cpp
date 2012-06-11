#include <boost/proto/debug.hpp>
#include <boost/test/unit_test.hpp>
#include <string>

#include <metaSMT/frontend/Logic.hpp>
#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/frontend/QF_UF.hpp>
#include <metaSMT/API/SymbolTable.hpp>
#include <metaSMT/API/Simplify.hpp>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::logic;
using namespace metaSMT::logic::QF_BV;
using namespace metaSMT::logic::QF_UF;
namespace proto = boost::proto;
using boost::dynamic_bitset;

BOOST_FIXTURE_TEST_SUITE(simplify_t, Solver_Fixture )

struct Lookup {
  std::map<unsigned, std::string> map_;

  std::string operator()(unsigned id) {
    return map_[id];
  }

  template < typename VarType >
  void insert(VarType var, std::string const &name) {
    map_.insert(std::make_pair(boost::proto::value(var).id, name));
  }
}; // Lookup

BOOST_AUTO_TEST_CASE( predicate_t ) {
  Lookup lookup;

  predicate a = new_variable();

  lookup.insert(a, "a");
  set_symbol_table( ctx, lookup);

  std::list<ContextType::result_type> Expr;

  Expr.push_back( evaluate(ctx, True ) );
  Expr.push_back( evaluate(ctx, False ) );
  Expr.push_back( evaluate(ctx, a ) );

  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_CASE( not_t ) {
  Lookup lookup;

  predicate a = new_variable();

  lookup.insert(a, "a");
  set_symbol_table( ctx, lookup);

  std::list<ContextType::result_type> Expr;

  Expr.push_back( evaluate(ctx, Not(True)) );
  Expr.push_back( evaluate(ctx, Not(False)) );
  Expr.push_back( evaluate(ctx, Not(a)) );
  Expr.push_back( evaluate(ctx, Not(Not(a))) );
  
  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_CASE( and_t ) {
  Lookup lookup;

  predicate a = new_variable();
  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();

  lookup.insert(a, "a");
  lookup.insert(b, "b");
  lookup.insert(c, "c");
  lookup.insert(d, "d");
  set_symbol_table( ctx, lookup);

  std::list<ContextType::result_type> Expr;

  Expr.push_back( evaluate(ctx, And(a,a)) );
  Expr.push_back( evaluate(ctx, And(a,b)) );
  Expr.push_back( evaluate(ctx, And(And(a,a), And(a,a))) );
  Expr.push_back( evaluate(ctx, And(And(a,b), And(a,b))) );
  Expr.push_back( evaluate(ctx, And(a, And(b, And(c,a)))) );
  Expr.push_back( evaluate(ctx, And(And(a,b), And(c,d))) );
  Expr.push_back( evaluate(ctx, And(True,And(And(a,b),And(True,d)))) );
  Expr.push_back( evaluate(ctx, And(True,And(And(a,b),And(False,d)))) );
  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_CASE( ite_t ) {
  Lookup lookup;

  predicate a = new_variable();
  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();

  lookup.insert(a, "a");
  lookup.insert(b, "b");
  lookup.insert(c, "c");
  lookup.insert(d, "d");
  set_symbol_table( ctx, lookup);

  std::list<ContextType::result_type> Expr;

  Expr.push_back( evaluate(ctx, Ite(True, a, b)) );
  Expr.push_back( evaluate(ctx, Ite(False, a, b)) );
  Expr.push_back( evaluate(ctx, Ite(c, a, a)) );

  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_CASE( equal_t ) {
  Lookup lookup;

  predicate a = new_variable();
  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();

  lookup.insert(a, "a");
  lookup.insert(b, "b");
  lookup.insert(c, "c");
  lookup.insert(d, "d");
  set_symbol_table( ctx, lookup);

  std::list<ContextType::result_type> Expr;

  Expr.push_back( evaluate(ctx, equal(True, a)) );
  Expr.push_back( evaluate(ctx, equal(False, a)) );
  Expr.push_back( evaluate(ctx, equal(a, True)) );
  Expr.push_back( evaluate(ctx, equal(a, False)) );
  Expr.push_back( evaluate(ctx, equal(a, a)) );
  Expr.push_back( evaluate(ctx, equal(a, b)) );
  Expr.push_back( evaluate(ctx, equal(And(a,a), And(a,a))) );
  Expr.push_back( evaluate(ctx, equal(And(a,b), And(a,b))) );

  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_CASE( nequal_t ) {
  Lookup lookup;

  predicate a = new_variable();
  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();

  lookup.insert(a, "a");
  lookup.insert(b, "b");
  lookup.insert(c, "c");
  lookup.insert(d, "d");
  set_symbol_table( ctx, lookup);

  std::list<ContextType::result_type> Expr;

  Expr.push_back( evaluate(ctx, nequal(True, a)) );
  Expr.push_back( evaluate(ctx, nequal(False, a)) );
  Expr.push_back( evaluate(ctx, nequal(a, True)) );
  Expr.push_back( evaluate(ctx, nequal(a, False)) );
  Expr.push_back( evaluate(ctx, nequal(a, a)) );
  Expr.push_back( evaluate(ctx, nequal(a, b)) );

  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_CASE( implies_t ) {
  Lookup lookup;

  predicate a = new_variable();
  predicate b = new_variable();
  predicate c = new_variable();
  predicate d = new_variable();

  lookup.insert(a, "a");
  lookup.insert(b, "b");
  lookup.insert(c, "c");
  lookup.insert(d, "d");
  set_symbol_table( ctx, lookup);

  std::list<ContextType::result_type> Expr;

  Expr.push_back( evaluate(ctx, implies(True, a)) );
  Expr.push_back( evaluate(ctx, implies(False, a)) );
  Expr.push_back( evaluate(ctx, implies(a, True)) );
  Expr.push_back( evaluate(ctx, implies(a, False)) );
  Expr.push_back( evaluate(ctx, implies(a, a)) );
  Expr.push_back( evaluate(ctx, implies(a, b)) );

  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_CASE( bvnot_t ) {
  Lookup lookup;

  bitvector a = new_bitvector();

  lookup.insert(a, "a");
  set_symbol_table( ctx, lookup);

  std::list<ContextType::result_type> Expr;

  Expr.push_back( evaluate(ctx, bvnot(bit0)) );
  Expr.push_back( evaluate(ctx, bvnot(bit1)) );
  Expr.push_back( evaluate(ctx, bvnot(bvnot(bit0))) );
  Expr.push_back( evaluate(ctx, bvnot(bvnot(bit1))) );
  Expr.push_back( evaluate(ctx, bvnot(a)) );
  Expr.push_back( evaluate(ctx, bvnot(bvnot(a))) );

  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_CASE( bv_constants ) {
  Lookup lookup;

  std::list<ContextType::result_type> Expr;

  Expr.push_back( evaluate(ctx, bit0) );
  Expr.push_back( evaluate(ctx, bit1) );
  Expr.push_back( evaluate(ctx, bvuint(0,1)) );
  Expr.push_back( evaluate(ctx, bvuint(1,1)) );

  Expr.push_back( evaluate(ctx, bvuint(2,2)) );
  Expr.push_back( evaluate(ctx, bvuint(3,2)) );
  Expr.push_back( evaluate(ctx, bvsint(0,1)) );
  Expr.push_back( evaluate(ctx, bvsint(1,1)) );

  Expr.push_back( evaluate(ctx, bvsint(2,2)) );
  Expr.push_back( evaluate(ctx, bvsint(3,2)) );
  Expr.push_back( evaluate(ctx, bvbin("0")) );
  Expr.push_back( evaluate(ctx, bvbin("1")) );

  Expr.push_back( evaluate(ctx, bvbin("10")) );
  Expr.push_back( evaluate(ctx, bvbin("11")) );
  Expr.push_back( evaluate(ctx, bvhex("0")) );
  Expr.push_back( evaluate(ctx, bvhex("1")) );
  Expr.push_back( evaluate(ctx, bvhex("2")) );
  Expr.push_back( evaluate(ctx, bvhex("3")) );
  Expr.push_back( evaluate(ctx, bvhex("A")) );
  Expr.push_back( evaluate(ctx, bvhex("F")) );

  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_CASE( bv_constants_overflow ) {
  Lookup lookup;

  std::list<ContextType::result_type> Expr;

  std::string const zero8_str = "0000" "0000";
  std::string const zero16_str = zero8_str + zero8_str;
  std::string const zero32_str = zero16_str + zero16_str;
  std::string const zero64_str = zero32_str + zero32_str;

  Expr.push_back( evaluate(ctx, bvadd(bvhex( zero8_str), bvhex( zero8_str))) );
  Expr.push_back( evaluate(ctx, bvadd(bvhex(zero16_str), bvhex(zero16_str))) );

  Expr.push_back( evaluate(ctx, bvadd(bvbin(zero32_str), bvbin(zero32_str))) );
  Expr.push_back( evaluate(ctx, bvadd(bvbin(zero64_str), bvbin(zero64_str))) );

  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_CASE( bv_arithmetic ) {
  Lookup lookup;

  unsigned const w = 8;
  bitvector x1 = new_bitvector(w);
  bitvector x2 = new_bitvector(w);
  bitvector x3 = new_bitvector(w);
  bitvector x4 = new_bitvector(w);
  lookup.insert(x1, "x1");
  lookup.insert(x2, "x2");
  lookup.insert(x3, "x3");
  lookup.insert(x4, "x4");
  set_symbol_table( ctx, lookup);

  std::list<ContextType::result_type> Expr;

  Expr.push_back( evaluate(ctx, bvadd(bit0, bit0)) );
  Expr.push_back( evaluate(ctx, bvadd(bit0, bit1)) );
  Expr.push_back( evaluate(ctx, bvadd(x1, bvuint(0,w))) );
  Expr.push_back( evaluate(ctx, bvadd(bvuint(0,w), x1)) );
  Expr.push_back( evaluate(ctx, bvadd(x1, x2)) );

  Expr.push_back( evaluate(ctx, bvsub(x1, bvuint(0,w))) );
  Expr.push_back( evaluate(ctx, bvsub(bvuint(0,w), x1)) );
  Expr.push_back( evaluate(ctx, bvsub(x1, x2)) );

  Expr.push_back( evaluate(ctx, bvmul(x1, bvuint(0,w))) );
  Expr.push_back( evaluate(ctx, bvmul(bvuint(0,w), x1)) );
  Expr.push_back( evaluate(ctx, bvmul(x1, x2)) );

  Expr.push_back( evaluate(ctx, bvudiv(x1, bvuint(0,w))) );
  Expr.push_back( evaluate(ctx, bvudiv(bvuint(0,w), x1)) );
  Expr.push_back( evaluate(ctx, bvudiv(x1, x2)) );

  Expr.push_back( evaluate(ctx, bvsdiv(x1, bvuint(0,w))) );
  Expr.push_back( evaluate(ctx, bvsdiv(bvuint(0,w), x1)) );
  Expr.push_back( evaluate(ctx, bvsdiv(x1, x2)) );

  Expr.push_back( evaluate(ctx, bvurem(x1, bvuint(0,w))) );
  Expr.push_back( evaluate(ctx, bvurem(bvuint(0,w), x1)) );
  Expr.push_back( evaluate(ctx, bvurem(x1, x2)) );

  Expr.push_back( evaluate(ctx, bvsrem(x1, bvuint(0,w))) );
  Expr.push_back( evaluate(ctx, bvsrem(bvuint(0,w), x1)) );
  Expr.push_back( evaluate(ctx, bvsrem(x1, x2)) );

  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_CASE( bv_comparison ) {
  Lookup lookup;

  unsigned const w = 8;
  bitvector x1 = new_bitvector(w);
  bitvector x2 = new_bitvector(w);
  lookup.insert(x1, "x1");
  lookup.insert(x2, "x2");
  set_symbol_table( ctx, lookup);

  std::list<ContextType::result_type> Expr;

  Expr.push_back( evaluate(ctx, And(bvslt(x1,x2), bvsgt(x1,x2))) );
  Expr.push_back( evaluate(ctx, Or(bvslt(x1,x2), bvsgt(x1,x2))) );
  Expr.push_back( evaluate(ctx, And(bvsle(x1,x2), bvsge(x1,x2))) );
  Expr.push_back( evaluate(ctx, Or(bvsle(x1,x2), bvsge(x1,x2))) );

  Expr.push_back( evaluate(ctx, And(bvult(x1,x2), bvugt(x1,x2))) );
  Expr.push_back( evaluate(ctx, Or(bvult(x1,x2), bvugt(x1,x2))) );
  Expr.push_back( evaluate(ctx, And(bvule(x1,x2), bvuge(x1,x2))) );
  Expr.push_back( evaluate(ctx, Or(bvule(x1,x2), bvuge(x1,x2))) );

  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_CASE( extend_expression_t ) {
  Lookup lookup;

  bitvector x = new_bitvector(8);
  bitvector y = new_bitvector(32);
  lookup.insert(x, "x");
  lookup.insert(y, "y");
  set_symbol_table( ctx, lookup);

  std::list<ContextType::result_type> Expr;

  Expr.push_back( evaluate(ctx, equal(y, sign_extend(24, x))) );
  Expr.push_back( evaluate(ctx, equal(x,  sign_extend(0, x))) );
  Expr.push_back( evaluate(ctx, equal(y, zero_extend(24, x))) );
  Expr.push_back( evaluate(ctx, equal(x,  zero_extend(0, x))) );

  for (std::list<ContextType::result_type>::const_iterator
	 it = Expr.begin(), ie = Expr.end();
       it != ie; ++it) {
    assumption(ctx, nequal(*it, simplify(ctx, *it)));
    BOOST_REQUIRE( !solve(ctx) );
  }
}

BOOST_AUTO_TEST_SUITE_END() //Solver

//  vim: ft=cpp:ts=2:sw=2:expandtab
