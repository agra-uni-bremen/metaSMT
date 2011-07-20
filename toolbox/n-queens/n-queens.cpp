#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/support/cardinality.hpp>
 
#include <metaSMT/support/run_algorithm.hpp>

#include <boost/mpl/vector.hpp>
#include <boost/format.hpp>
#include <boost/foreach.hpp>

using namespace metaSMT;
using namespace metaSMT::logic;
using namespace metaSMT::solver;
using namespace std; 

#define foreach BOOST_FOREACH 

template<typename Solver>
struct nqueens
{
  typedef bool result_type;
  
  nqueens ( unsigned size ) 
  {
    field_size = size; 
    
    init_field (); 
    field_constraints();
  }

  bool operator() ()
  {
    std::cout << "Solving" << std::endl; 
    bool sat = solve(ctx);
    if(sat) print_solution();
    return sat; 
  }

  void init_field () 
  {
    field.resize ( field_size ); 

    foreach ( vector<predicate>& row, field )
    {
      row.clear ();
      for ( unsigned i = 0; i < field_size; i++ )
      {
        row.push_back ( new_variable () ); 
      }
    }
  }

  void field_constraints() 
  {
    for ( unsigned i = 0; i < field_size; ++i )
    {
      row ( i );
      column ( i );

      if(i != 0) 
      {
      	falling ( i, 0 );
        rising ( field_size-1, i );
      }
      rising ( i, 0 );
      falling ( 0 , i );
     
    }
  }

  void falling(unsigned row, unsigned col)
  {
    std::vector<predicate> vec1;
    while( row < field_size && col < field_size)
    {
    
      vec1.push_back(field[row][col]);
      
      col++;
      row++;
    }
    if( vec1.size() > 1 )
    {
      assertion( ctx, cardinality_leq( ctx, vec1, 1));
    }
  }

  void rising(int row, int col)
  {
    std::vector<predicate> vec1;
    while ( row >= 0 && col < field_size  )
    {
      vec1.push_back(field[row][col]);
      row--;
      col++;
    }
    if(vec1.size() > 1)
    {
      assertion( ctx, cardinality_leq( ctx, vec1, 1));
    }
  }

  void row ( unsigned row )
  {
    assertion ( ctx, one_hot( ctx , field[row] ) ); 
  }

  void column ( unsigned col )
  {
    std::vector<predicate> vec1;
    for ( unsigned i = 0; i < field_size; i++ )
    {
      vec1.push_back(field[i][col]);
     
    }
    assertion( ctx, one_hot( ctx, vec1));
    
  }


  void print_solution()
  {
    for (unsigned i = 0; i < field_size; ++i) {
      for (unsigned k = 0; k < field_size; ++k) {
        bool val = read_value(ctx, field[i][k]);
        printf("%d", val);
      }
      printf("\n");
    }
  }

  Solver ctx; 
  unsigned field_size; 
  vector < vector < predicate > > field; 
};

int
main(int argc, const char *argv[])
{
  typedef mpl::vector < 
      DirectSolver_Context < Boolector >
      > SolverVec;

  if( argc < 2) {
    cout << "usage: "<< argv[0] << " <size of the field>" << endl;
    exit(1);
  }

  unsigned solver = 0; //atoi ( argv[1] ); 
  unsigned size = atoi ( argv[1] ); 


  bool val = run_algorithm<SolverVec, nqueens> ( solver, size ); 

  std::cout << "found solution? " << (val ? "yes" : "no") << std::endl;

  return 0;
}

