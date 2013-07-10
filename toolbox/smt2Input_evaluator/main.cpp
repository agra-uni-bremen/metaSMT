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
  int const STREAM_SIZE = 65535;
  typedef UTreeEvaluator<ContextType> Evaluator;
  char inputline[STREAM_SIZE];
  string line;
  stringstream *buf = new stringstream;
  ContextType ctx;
  Evaluator evaluator(ctx);
  SMT2Parser<Evaluator> parser(evaluator);
  while(!cin.eof()){
    cin.getline(inputline,STREAM_SIZE);
    assert( !std::cin.fail() );
    if ( std::cin.fail() ) {
      std::cerr << "Error during input operation, e.g., stream size is too low" << '\n';
      return -1;
    }
    line = inputline;
    // std::cerr << line << '\n';
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
