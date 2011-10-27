#define BOOST_TEST_MODULE test_graph
#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/Graph_Context.hpp>
#include <metaSMT/support/SMT_File_Writer.hpp>
#include <boost/assign/std/vector.hpp>
#include <boost/proto/debug.hpp>
#include <boost/test/unit_test.hpp>
#include <string>

using namespace std;
using namespace metaSMT;
using namespace logic;
using namespace logic::QF_BV;
namespace proto = boost::proto;

class Graph_Fixture {
  protected:
    Graph_Context ctx;
};

BOOST_FIXTURE_TEST_SUITE(test_graph, Graph_Fixture )

BOOST_AUTO_TEST_CASE( write_smt_file )
{
  using namespace boost::assign;

  vector<SMT_Expression> assertions;
  bitvector x = new_bitvector(1);
  bitvector y = new_bitvector(1);
  bitvector z = new_bitvector(1);
  bitvector r = new_bitvector(4);

  predicate p = new_variable();

  assertions += evaluate( ctx, equal(x, bvnot(y)) );
  assertions += evaluate( ctx, equal(z, bvnot(bvnot(z))) );
  assertions += evaluate( ctx, equal(x, z) );
  assertions += evaluate( ctx, nequal(x, y) );
  assertions += evaluate( ctx, equal(bit1, bit1) );
  assertions += evaluate( ctx, equal(bit0, bit0) );

  assertions += evaluate( ctx, equal(bvand(x, x), bvand(x, x)) );
  assertions += evaluate( ctx, equal(bvor(x, x), bvor(x, x)) );
  assertions += evaluate( ctx, equal(bvnand(x, x), bvnand(x, x)) );
  assertions += evaluate( ctx, equal(bvnor(x, x), bvnor(x, x)) );
  assertions += evaluate( ctx, equal(bvxor(x, x), bvxor(x, x)) );
  assertions += evaluate( ctx, equal(bvxnor(x, x), bvxnor(x, x)) );

  assertions += evaluate( ctx, equal(bvadd(x, x), bvadd(x, x)) );
  assertions += evaluate( ctx, equal(bvsub(x, x), bvsub(x, x)) );
  assertions += evaluate( ctx, equal(bvmul(x, x), bvmul(x, x)) );

  assertions += evaluate( ctx, equal(bvsle(x, x), bvsle(x, x)) );
  assertions += evaluate( ctx, equal(bvslt(x, x), bvslt(x, x)) );
  assertions += evaluate( ctx, equal(bvsge(x, x), bvsge(x, x)) );
  assertions += evaluate( ctx, equal(bvsgt(x, x), bvsgt(x, x)) );
  assertions += evaluate( ctx, equal(bvule(x, x), bvule(x, x)) );
  assertions += evaluate( ctx, equal(bvult(x, x), bvult(x, x)) );
  assertions += evaluate( ctx, equal(bvuge(x, x), bvuge(x, x)) );
  assertions += evaluate( ctx, equal(bvugt(x, x), bvugt(x, x)) );

  assertions += evaluate( ctx, equal( bit1, bvcomp(x, x) ));
  assertions += evaluate( ctx, implies(p, p) );
  assertions += evaluate( ctx, equal(And(p, p), And(p, p)) );
  assertions += evaluate( ctx, equal(Or(p, p), Or(p, p)) );
  assertions += evaluate( ctx, equal(Xor(p, p), Xor(p, p)) );
  assertions += evaluate( ctx, equal(Nand(p, p), Nand(p, p)) );
  assertions += evaluate( ctx, equal(Nor(p, p), Nor(p, p)) );
  assertions += evaluate( ctx, equal(Xnor(p, p), Xnor(p, p)) );
  assertions += evaluate( ctx, equal(p, True) );
  assertions += evaluate( ctx, nequal(p, False) );
  assertions += evaluate( ctx, nequal(p, Not(p)) );
  assertions += evaluate( ctx, Ite(p, equal(x, x), equal(x, y)));

  assertions += evaluate( ctx, equal(bvint(10,5), bvint(10,5)) );
  assertions += evaluate( ctx, equal(r, bvsint(-2,4)) );
  assertions += evaluate( ctx, equal(bvhex("FF"), bvhex("FF")) );
  assertions += evaluate( ctx, equal(bvbin("1"), bvbin("1")) );
  assertions += evaluate( ctx, equal(bvbin("101"), bvbin("101")) );

  std::ofstream file("test.smt");
  write_smt(file, ctx.graph(), assertions);
}

BOOST_AUTO_TEST_CASE( syntax )
{
  bitvector x = new_bitvector(1);
  evaluate(ctx, x);
  evaluate(ctx, bvnot(x) );
  evaluate(ctx, bvnot(bvnot(x)) );
  evaluate(ctx, x);
  evaluate(ctx, bit1);
  evaluate(ctx, bit1);
  evaluate(ctx, bvnot(bit0));
  evaluate(ctx, bvint ( 1, 1));
  evaluate(ctx, bvint ( 0, 1));
  evaluate(ctx, bvuint( 1, 1));
  evaluate(ctx, bvuint( 0, 1));
  evaluate(ctx, bvsint(-1, 1));
  evaluate(ctx, bvsint( 0, 1));
  evaluate(ctx, bvbin ("1")  );
  evaluate(ctx, bvbin ("0") );
  evaluate(ctx, bvbin ("0") );
  evaluate(ctx, bvnand( bit0, bit1 ) );
  evaluate(ctx, bvnot(bvnand( bit0, bit1 )) );
  evaluate(ctx, bvxor(bvnand( bit0, bit1 ), bit1) );

  SMT_Expression e = evaluate( ctx, bvxor(bit1, bit1) );
  evaluate ( ctx, bvnot(e) );
  evaluate( ctx, equal(bit1, bit1) );
  evaluate( ctx, nequal(bit1, x) );

}

BOOST_AUTO_TEST_SUITE_END() //QF_BV

//  vim: ft=cpp:ts=2:sw=2:expandtab
