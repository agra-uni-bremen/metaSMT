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
  char inputline[1024];
  string line;
  stringstream *buf = new stringstream;
  ContextType ctx;
  Evaluator evaluator(ctx);
  SMT2Parser<Evaluator> parser(evaluator);
  while(!cin.eof()){
    cin.getline(inputline,1024);
    line = inputline;
    *buf << line << endl;
    size_t found = line.find("(get-value");
    if(line.compare("(check-sat)") == 0 || found != line.npos){
      boost::spirit::utree::list_type ast;
      parser.parse(*buf, ast);
      evaluator.evaluateInstance(ast);
      delete buf;
      buf = new stringstream;
    }
    if(line.compare("(exit)") == 0){
      break;
    }
  }
  return 0;
}
