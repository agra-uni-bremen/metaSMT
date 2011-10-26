#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/backend/SWORD_Backend.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/support/run_algorithm.hpp>

#include <boost/mpl/vector.hpp>
#include <boost/format.hpp>

 
using namespace metaSMT;
using namespace metaSMT::logic;
using namespace metaSMT::logic::QF_BV;
using namespace metaSMT::solver;
using namespace std; 


template<typename Solver>
struct my_algo
{
  typedef int result_type;

  my_algo ( unsigned width ) :
    width_ (width) {}; 

  result_type operator()() 
  {
    const unsigned width = width_;

    bitvector a = new_bitvector(width);
    bitvector b = new_bitvector(width);
    bitvector c = new_bitvector(2*width);

    bitvector zero = new_bitvector(width);
    assertion( ctx, equal(zero, bvuint(0,width)) );
    assertion( ctx, nequal(a, bvuint(1,width)) );
    assertion( ctx, nequal(b, bvuint(1,width)) );

    assertion( ctx, equal(c, bvmul( concat(zero, a), concat(zero,b)) ));

    int valids = 0; 
    for (unsigned i = 0; i < 10; i++) 
    {
      unsigned r = (unsigned long long)rand()%(1ull<<width);
      assumption( ctx, equal(c, bvuint(r, 2*width)) );

      if( solve( ctx) ) {
        unsigned a_value = read_value ( ctx, a );
        unsigned b_value = read_value ( ctx, b ); 

        std::cout << "factorized " << r << " into " << a_value << " * " << b_value << std::endl;
        valids++; 
      } else {
        std::cout << boost::format("could not factorize %u") % r << std::endl;
      }
    }


    return valids; 
  }

  Solver ctx;
  unsigned width_; 
};



#include <iostream>
using namespace std;

int main(int argc, const char *argv[])
{
  typedef mpl::vector2 < 
    DirectSolver_Context< SWORD_Backend >
  , DirectSolver_Context< Z3_Backend > 
  > SolverVec;

  if( argc < 3) {
    cout << "usage: example3 solver width\nsolver:\n\t0 - SWORD\n\t1 - Z3" << endl;
    exit(1);
  }


  unsigned solver = atoi ( argv[1] ); 
  unsigned width  = atoi ( argv[2] ); 

  int val = run_algorithm<SolverVec, my_algo> ( solver, width );

  cout << "Got " << val << endl;
  
  
  return 0;
}
