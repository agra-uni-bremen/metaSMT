#include <metaSMT/support/parser/SMT2Parser.hpp>
#include <metaSMT/support/parser/UTreeEvaluator.hpp>

#include <string>
#include <fstream>

using namespace std;
using namespace metaSMT;
using namespace metaSMT::solver;
using namespace metaSMT::evaluator;
using namespace metaSMT::smt2;

int main(int argc, char **argv) {
  typedef UTreeEvaluator<ContextType> Evaluator;
  string line;
  stringstream *buf = new stringstream;
  ContextType ctx;
  Evaluator evaluator(ctx);
  SMT2Parser<Evaluator> parser(evaluator);
  while( !cin.eof() ){
    std::getline(std::cin, line);
    if ( std::cin.fail() ) {
      // stream end without exit or read error
      return 0;
    }

    // std::cerr << line << '\n';
    *buf << line << endl;
    size_t found = line.find("(get-value");
    if (line == "(check-sat)" || found != line.npos) {
      boost::spirit::utree::list_type ast;
      parser.parse(*buf, ast);
      evaluator.evaluateInstance(ast);
      delete buf;
      buf = new stringstream;
    }

    if ( line == "(exit)" ) {
      break;
    }
  }
  return 0;
}
