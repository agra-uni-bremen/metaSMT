
#include <iostream>
#include <string>

#include <metaSMT/frontend/QF_BV.hpp>

#include <metaSMT/io/DimacsParser.hpp>

#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/SAT_Clause.hpp>
#include <metaSMT/backend/PicoSAT.hpp>
#include <metaSMT/BitBlast.hpp>

#include <boost/format.hpp>
#include <boost/foreach.hpp>
#include <boost/timer.hpp>


using namespace metaSMT; 
using namespace metaSMT::dimacs;
using namespace metaSMT::solver;
using namespace std; 

int main(int argc, const char *argv[])
{
  assert ( argc == 2 ); 

  string filename ( argv[1] ); 

  ifstream stream ( filename.c_str() ); 
  assert ( stream.good() ); 

  DirectSolver_Context < BitBlast < SAT_Clause < PicoSAT > > > picosat;

  boost::timer all_timer;

  bool r = parse_dimacs ( stream, picosat );

  if ( r ) 
  {
    cout << boost::format ("c Parsed in %.2f seconds.") % all_timer.elapsed() << std::endl;
  }
  else
  {
    cerr << boost::format ("c Failure while parsing Dimacs file %s.") % filename << endl;
    return -1; 
  }

  bool sat = solve ( picosat);

  if ( sat ) 
    std::cout << "s SATISFIABLE" << std::endl;
  else
    std::cout << "s UNSATISFIABLE" << std::endl;

  return EXIT_SUCCESS;
}
