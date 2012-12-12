#include <metaSMT/support/parser/SMT2Parser.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>
#include <metaSMT/support/parser/UTreeEvaluator.hpp>
#include <metaSMT/support/parser/UTreeEvaluatorToCode.hpp>

#include <string>
#include <fstream>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::evaluator;
using namespace metaSMT::smt2;

int main(int argc, char **argv)
{
  if (argc < 2) {
    cerr << "pls enter .smt2 Filename" << endl;
    return -1;
  } else if (argc > 2) {
    cerr << "ignoring Parameters > 2" << endl;
  }

  char *filename = argv[1];
  fstream input;
  input.open(filename);
  if (!input) {
    cerr << "failed to read file: " << filename << endl;
    return -1;
  }

  std::stringstream buf;
  while (!input.eof()) {
    string line;
    getline(input, line);
    line += "\n";
    buf << line;
  }

  typedef DirectSolver_Context<Stack<Z3_Backend> > Context;
  typedef UTreeEvaluator<Context> Evaluator;

  Context ctx;
  Evaluator evaluator(ctx);
  boost::spirit::utree::list_type ast;
  SMT2Parser<Evaluator> parser(ast, evaluator);
  parser.parse(buf, ast);
  evaluator.printSMT(ast);

  return 0;
}
