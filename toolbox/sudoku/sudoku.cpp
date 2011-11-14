
#include <metaSMT/frontend/QF_BV.hpp>
 
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/GraphSolver_Context.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/backend/MiniSAT.hpp>
#include <metaSMT/backend/PicoSAT.hpp>
#include <metaSMT/backend/CUDD_Context.hpp>
#include <metaSMT/backend/SAT_Aiger.hpp>
 
#include <metaSMT/BitBlast.hpp>
#include <metaSMT/support/run_algorithm.hpp>

#include <boost/mpl/vector.hpp>
#include <boost/format.hpp>
#include <boost/foreach.hpp>

using namespace metaSMT;
using namespace metaSMT::logic;
using namespace metaSMT::logic::QF_BV;
using namespace metaSMT::solver;
using namespace std; 

#define foreach BOOST_FOREACH 

template<typename Solver>
struct sudoku
{
  typedef bool result_type;
  
  sudoku ( string problem ) 
  {
    field_size = 16; 
    bit_width = int(ceil ( log ( field_size ) / log ( 2 ) )); 
    block_width = bit_width; 
    
    init_field (); 
    parse ( problem ); 
    field_constraints();
  }

  void parse ( string problem )
  {
    unsigned x = 0, y = 0;

    foreach ( char c, problem )
    {
      if ( c != '_') 
      {
        assertion ( ctx, 
            equal ( field[x][y], bvuint ( c - 'a', bit_width ) ) ); 
      }

      ++x;
      if ( x == field_size )
      {
        y++;
        x = 0; 
      }
    }
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

    foreach ( vector<bitvector>& row, field )
    {
      row.clear ();
      for ( unsigned i = 0; i < field_size; i++ )
      {
        row.push_back ( new_bitvector ( bit_width ) ); 
      }
    }
  }

  void field_constraints() 
  {
    for ( unsigned i = 0; i < field_size; ++i )
    {
      row ( i );
      column ( i ); 
    }

    for ( unsigned i = 0; i < block_width; i++ )
    {
      for ( unsigned j = 0; j < block_width; j++ )
      {
        block ( i*block_width, j*block_width ); 
      }
    }


  }
  
  void row ( unsigned row )
  {
    for ( unsigned i = 0; i < field_size; i++ )
    {
      for ( unsigned j = i + 1; j < field_size; ++j )
      {
        assertion ( ctx, 
            nequal ( field[row][i], field[row][j] ) ); 
      }
    }
  }

  void column ( unsigned col )
  {
    for ( unsigned i = 0; i < field_size; i++ )
    {
      for ( unsigned j = i + 1; j < field_size; ++j )
      {
        assertion ( ctx, 
            nequal ( field[i][col], field[j][col] ) ); 
      }
    }
  }

  // gets the i-th element of block at pos (col, row)
  bitvector& index (unsigned row, unsigned col, unsigned i)
  {
    return field[row + i/block_width][col + i%block_width];  
  }

  void block ( unsigned col, unsigned row )  
  {
    for ( unsigned i = 0; i < field_size; i++ )
    {
      for ( unsigned j = i + 1; j < field_size; ++j )
      {
        assertion ( ctx, 
            nequal ( index(row, col, i), index(row, col, j) ) ); 
      }
    }
         
  }

  void print_solution()
  {
    for (unsigned i = 0; i < field_size; ++i) {
      if( i % block_width == 0) printf("\n");
      for (unsigned k = 0; k < field_size; ++k) {
        if( k % block_width == 0 ) printf(" ");
        unsigned val = read_value(ctx, field[i][k]);
        printf("%c", 'a'+val);
      }
      printf("\n");
    }
    printf("\n");
  }

  Solver ctx; 
  unsigned field_size; 
  unsigned bit_width; 
  unsigned block_width; 
  vector < vector < bitvector > > field; 


};

int
main(int argc, const char *argv[])
{
  typedef mpl::vector < 
      DirectSolver_Context < Boolector >
    , DirectSolver_Context < BitBlast < SAT_Aiger < MiniSAT > > >
    , DirectSolver_Context < BitBlast < SAT_Aiger < PicoSAT > > >
    , DirectSolver_Context < BitBlast < CUDD_Context > >
 
    , GraphSolver_Context < Boolector >
    , GraphSolver_Context < BitBlast < SAT_Aiger < MiniSAT > > >
    , GraphSolver_Context < BitBlast < SAT_Aiger < PicoSAT > > >
    , GraphSolver_Context < BitBlast < CUDD_Context > >
     
      > SolverVec;

  if( argc < 2) {
    cout << "usage: "<< argv[0] << "  solver sudoku\nsolver:\n\t0 - Boolector (SMT)\n\t1 - MiniSAT (SAT)\n\t2 - PicoSAT (SAT)\n\t3 - CUDD (BDD)" << endl;
    exit(1);
  }

  unsigned solver = atoi ( argv[1] ); 

  bool val = run_algorithm<SolverVec, sudoku> ( solver, argv[2] ); 

  std::cout << "Sudoku valid? " << (val ? "yes" : "no") << std::endl;

  return val? 0 : 1;
}

