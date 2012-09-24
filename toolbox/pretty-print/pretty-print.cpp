#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/ExpressionSolver.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>

#include <metaSMT/frontend/Logic.hpp>
#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/frontend/Array.hpp>

#include <metaSMT/expression/expression.hpp>
#include <metaSMT/expression/pretty_printing.hpp>
#include <metaSMT/expression/print_expression.hpp>
#include <metaSMT/support/DefaultSymbolTable.hpp>

using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::logic;
using namespace metaSMT::logic::QF_BV;
using namespace metaSMT::logic::Array;
using namespace metaSMT::expression;

struct Lookup {
  std::map<unsigned, std::string> map_;

  std::string operator()(unsigned id) {
    return map_[id];
  }

  template < typename T >
  void insert(T const &v, std::string const &name) {
    map_.insert(std::make_pair(boost::proto::value(v).id, name));
  }
};

struct Printer {
  Printer(std::ostream &os, Lookup &table)
    : os(os)
    , table(table)
  {}

  template < typename T >
  std::ostream &operator<<(T expr);

  std::ostream &os;
  Lookup &table;
}; // Printer

template < typename T >
std::ostream &Printer::operator<<(T expr) {
  return os;
}

template <>
std::ostream &Printer::operator<<(logic_expression expr) {
  std::ostream_iterator<char> out_it( os );
  expression::print_expression_static(
    out_it, expr, table
  );
  return os;
}

int main( int argc, char *argv[] ) {
  typedef DirectSolver_Context<
    ExpressionSolver< Z3_Backend >
  > ContextType;
  typedef ContextType::result_type result_type;

  ContextType ctx;
  Lookup lookup;

  Printer err(std::cerr, lookup);

  predicate x = new_variable();
  lookup.insert(x, "x");
  err << evaluate(ctx, x) << '\n';

  predicate y = new_variable();
  lookup.insert(y, "y");
  result_type expr = evaluate(ctx, And(x, y));
  err << expr << '\n';

  unsigned const elem_width = 8;
  unsigned const index_width = 5;
  array a = new_array(elem_width, index_width);
  lookup.insert(a, "a");
  err << evaluate(ctx, a) << '\n';

  bitvector index = new_bitvector(index_width);
  lookup.insert(index, "index");
  err << evaluate(ctx, store(a, index, new_bitvector(elem_width))) << '\n';
  err << evaluate(ctx, select(a, index)) << '\n';

  return 0;
}
