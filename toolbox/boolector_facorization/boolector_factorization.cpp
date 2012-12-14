#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/frontend/QF_BV.hpp>

#include <boost/timer.hpp>
#include <iostream>

static unsigned width = 32;

static const unsigned repeat= 10;
static const unsigned limit = 10000;

static unsigned data[limit];

static unsigned all_valids = 0;

int run_metaSMT () {
  using namespace metaSMT;
  using namespace metaSMT::logic;
  using namespace metaSMT::logic::QF_BV;


  metaSMT::DirectSolver_Context<metaSMT::solver::Boolector> ctx;

  bitvector a = new_bitvector(width);
  bitvector b = new_bitvector(width);
  bitvector c = new_bitvector(2*width);

  bitvector zero = new_bitvector(width);
  assertion( ctx, equal(zero, bvuint(0,width)) );
  assertion( ctx, nequal(a, bvuint(1,width)) );
  assertion( ctx, nequal(b, bvuint(1,width)) );

  assertion( ctx, equal(c, bvmul( concat(zero, a), concat(zero,b)) ));

  int valids = 0; 
  for (unsigned i = 0; i < limit; ++i) {
    assumption( ctx, equal(c, bvuint(data[i], 2*width)) );

    if( solve( ctx) ) {
      valids++; 
    }
  }

  return valids; 
}

int run_btor () {

  Btor* btor = boolector_new();
  boolector_enable_inc_usage(btor);
  boolector_enable_model_gen(btor);

  BtorNode* a = boolector_var(btor, width, "a");
  BtorNode* b = boolector_var(btor, width, "b");
  BtorNode* c = boolector_var(btor, 2*width, "c");

  BtorNode* zero = boolector_var(btor,width, "zero");
  boolector_assert( btor, boolector_eq(btor, zero, boolector_zero(btor, width)) );
  boolector_assert( btor, boolector_ne(btor, a, boolector_unsigned_int(btor, 1, width)) );
  boolector_assert( btor, boolector_ne(btor, b, boolector_unsigned_int(btor, 1, width)) );

  boolector_assert( btor, boolector_eq(btor,
        c, boolector_mul(btor,
          boolector_concat(btor, zero, a),
          boolector_concat(btor, zero, b)) 
        ));

  int valids = 0; 
  for (unsigned i = 0; i < limit; ++i) {
    boolector_assume( btor, boolector_eq(btor, c, 
          boolector_unsigned_int(btor, data[i], 2*width)) );

    if( boolector_sat( btor ) == BOOLECTOR_SAT ) {
      valids++; 
    }
  }
  
  boolector_delete(btor);
  return valids; 
}


double run( 
      int (fun) ()
  )
{
  boost::timer timer;
  timer.restart();
  for (unsigned i = 0; i < repeat; ++i) {
    all_valids += fun();
  }
  return timer.elapsed();
}

void result( std::string const & name, double time) {
  std::cout << name << " ran " << (limit*repeat) << " in " 
    << time << "s" 
    << " (" << limit << " in " << (time/repeat) <<"s"
    << ", 1 in " << (time/repeat/limit) <<"s"
    << ")"
    << std::endl;
}

int main(int argc, const char *argv[])
{
  if(argc != 2) {
    std::cout << "usage: " << argv[0] << " <magic number> # even = boolector;metaSMT, odd = metaSMT;boolector " << std::endl;
    exit(1);
  }
  
  time_t seed = time(0);
  srand(seed);
  std::cout << "seed: " << seed << std::endl; 

  std::vector<unsigned> data (limit);
  for (unsigned i = 0; i < limit; ++i) {
    data[i] = (unsigned long long)rand()%(1ull<<(width+1));
  }

  double mtime=0.0;
  double btime=0.0;

  if ( atoi(argv[1]) & 1u) {

  std::cout << "Running metaSMT" << std::endl;
  mtime = run(run_metaSMT);

  std::cout << "Running Boolector" << std::endl;
  btime = run( run_btor);
  } else {

  std::cout << "Running Boolector" << std::endl;
  btime += run( run_btor);

  std::cout << "Running metaSMT" << std::endl;
  mtime += run(run_metaSMT);

  }

  result( "metaSMT", mtime);
  result( "boolector", btime);

  return  mtime + btime + all_valids == 0;
}
