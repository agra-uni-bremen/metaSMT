#include <metaSMT/frontend/QF_BV.hpp>
 
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/backend/SAT_Clause.hpp>
#include <metaSMT/backend/MiniSAT.hpp>
#include <metaSMT/backend/PicoSAT.hpp>
#include <metaSMT/backend/CUDD_Context.hpp>

 
#include <metaSMT/BitBlast.hpp>
#include <metaSMT/support/run_algorithm.hpp>

#include <boost/mpl/vector.hpp>
#include <boost/format.hpp>
#include <boost/foreach.hpp>
#include <boost/bimap.hpp>
#include <boost/timer.hpp>

using namespace metaSMT;
using namespace metaSMT::logic;
using namespace metaSMT::logic::QF_BV;
using namespace metaSMT::solver;
using namespace std; 

#define foreach BOOST_FOREACH 


typedef std::vector<unsigned> guess_type;


class secret {
  public:
    secret ( unsigned width=4, unsigned noptions=6) 
    : _noptions(noptions), _solution(width)
    { 
      foreach( unsigned & v, _solution) {
        v = rand() % noptions;
      }
      //for (unsigned i = 0; i < width; ++i) {
      //  _solution[i] = (1+i)%noptions;
      //}
    }

    unsigned options() { return _noptions; }
    unsigned width() { return _solution.size(); }

    std::pair<unsigned, unsigned> check( guess_type const & guess )
    {
      unsigned correct = 0;
      unsigned wrong_place = 0;

      assert(guess.size() == _solution.size() );

      std::vector<int> count( _noptions, 0);

      for (unsigned i = 0; i < _solution.size(); ++i) {
        if ( guess[i] == _solution[i] ) {
          ++ correct;
        }
        ++ count[ guess[i] ];
      }

      foreach( unsigned v, _solution) {
        if( count[v] >0 ) {
          ++wrong_place;
          --count[v];
        }
      }


      return std::make_pair(correct, wrong_place-correct);
    }

    template <typename O>
    friend O & operator<< (O& o, secret  const & s) {
      bool next=false;
      foreach( unsigned v, s._solution) {
        if(next) o << ", ";
        else next =true;
        o << v;

      }
      return o;
    }

  private:
    const unsigned _noptions;
    std::vector<unsigned> _solution;

};

template<typename Solver>
struct guesser
{
  guesser( unsigned width, unsigned noptions) 
    : _secret(width, noptions)
    , _bitwidth( _secret.options() )
  { 
    init_solver();
  }

  typedef bool result_type;

  result_type operator() () {
    boost::timer all_timer;

    boost::format fmt(" -> %2u / %2u ");

    guess_type guess( _secret.width() );
    //for (unsigned i = 0; i < 20; ++i) {
    for (unsigned i = 0; true; ++i) {
      boost::timer cur_timer;
      if( ! solve(_solver) ) {
        std::cout << "problem instance unsatisfiable!" << std::endl;
        break;
      }
      double cur_t = cur_timer.elapsed();
      cout << "guess " << boost::format("%2u")%i << ":";
      for (unsigned k = 0; k < _secret.width(); ++k) {
        guess[k] = read_value( _solver, _vars[k]);
        cout << " " << boost::format("%2u") % guess[k];
      }
      cout.flush();
      unsigned correct, wrong_place;
      boost::tie( correct, wrong_place) = _secret.check(guess);
      std::cout 
        << fmt % correct % wrong_place 
        << boost::format(" (%3.2fs, %3.2fs)")
          % cur_t
          % all_timer.elapsed()
        << std::endl;
      if( correct == _secret.width()) {
        return true;
      } else {
        block_correct( guess, correct);
        if( wrong_place > 0) {
          block_wrong_place( guess, correct + wrong_place);
        }
      }
    }
      
    return false;
  }

  void init_solver() {
    for (unsigned i = 0; i < _secret.width(); ++i) {
      _vars.push_back( new_bitvector( _bitwidth ) );
      metaSMT::assertion ( _solver, bvult( _vars[i], 
          bvuint( _secret.options(), _bitwidth)) );
    }
  }

  void block_correct( guess_type const & guess
    , unsigned correct
  ) {
    unsigned width = _secret.width();

    typename Solver::result_type sum_equal = evaluate( _solver, bvuint(0 , width));
    for (unsigned i = 0; i < width; ++i) {
      sum_equal = evaluate( _solver, bvadd( sum_equal, 
        zero_extend(width-1, bvcomp( _vars[i], bvuint( guess[i], _bitwidth)))
        ));
    }
    metaSMT::assertion( _solver, metaSMT::logic::equal( sum_equal, bvuint( correct, width)));
    metaSMT::assertion( _solver, nequal( sum_equal, bvuint( width, width)));
  }

  void block_wrong_place( guess_type const & guess
    , unsigned anywhere
  ) {
    unsigned width   = _secret.width();
    unsigned options = _secret.options();

    std::vector<unsigned> by_color ( options, 0);
    foreach( unsigned g, guess) {
      ++by_color[g];
    }

    std::vector< typename Solver::result_type> count_by_color( options,
        evaluate( _solver, bvuint(0 , width)));

    for (unsigned i = 0; i < width; ++i) {
      // iterate over all variables
      // and count by colors if less than by_color

      for (unsigned c = 0; c < options; ++c) {
        count_by_color[c] = evaluate( _solver,
            Ite( 
                And( metaSMT::logic::equal(_vars[i], bvuint( c, _bitwidth) ), 
                   bvult(count_by_color[c], bvuint( by_color[c], width)))
              , bvadd( count_by_color[c], bvuint(1, width))
              , count_by_color[c]
            ));
      }
    }

    
    typename Solver::result_type sum = evaluate( _solver, bvuint(0 , width));
    foreach( typename Solver::result_type r, count_by_color) {
      sum = evaluate(_solver, bvadd( sum, r)); 
    }

    metaSMT::assertion( _solver, metaSMT::logic::equal(sum, bvuint(anywhere, width)) );
  }


  secret _secret;
  Solver _solver;
  std::vector< bitvector > _vars;
  unsigned _bitwidth;
};

int
main(int argc, const char *argv[])
{
  FILE *dev_urandom;
  uint32_t seed;
  if((dev_urandom = fopen("/dev/urandom", "r")) == NULL) return 2;
  if(fread(&seed, sizeof(seed), 1, dev_urandom) == 0) return 3;
  if(fclose(dev_urandom) != 0) return 4;
  srand( seed );
  typedef mpl::vector < 
      DirectSolver_Context < Boolector >
    , DirectSolver_Context < BitBlast < SAT_Clause < MiniSAT > > >
    , DirectSolver_Context < BitBlast < SAT_Clause < PicoSAT > > >
    , DirectSolver_Context < BitBlast < CUDD_Context > >
    > SolverVec;

  if( argc < 2) {
    cout << "usage: "<< argv[0] << "  solver ?width ?options\nsolver:\n\t0 - Boolector (SMT)\n\t1 - MiniSAT (SAT)\n\t2 - PicoSAT (SAT)\n\t3 - CUDD (BDD)" << endl;
    exit(1);
  }

  unsigned solver = atoi ( argv[1] ); 
  unsigned width = (argc > 2) ? atoi(argv[2]) : 4;
  unsigned options = (argc > 3) ? atoi(argv[3]) : 6;

  bool val = run_algorithm<SolverVec, guesser> ( solver, width, options ); 

  std::cout << "secret guessed? " << (val ? "yes" : "no") << std::endl;

  return val ? 0 : 1;
}

