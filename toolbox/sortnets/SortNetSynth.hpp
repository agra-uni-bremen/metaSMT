#include "Level.hpp"
#include "SynthNet.hpp"

#include <boost/foreach.hpp>

#include <iostream>

using metaSMT::logic::predicate;

template<typename Solver, typename VerifyerContext>
struct SortNetSynth
{
  typedef bool result_type;

  unsigned size;
  SynthNet<Solver> syn_net;

  typedef std::list< Level > Net;
  Net ver_net;

  double time_synth;
  double time_verify;

  SortNetSynth ( unsigned min_depth, std::vector<std::string> const & inits )
  : size(inits[0].size())
  , syn_net(size)
  {
    for (unsigned i = 0; i < min_depth; i++) {
      syn_net.add_level();
    }
    BOOST_FOREACH (std::string const & init, inits) {
      syn_net.add_counterexample(init);
    }
  }

  void print_solution(std::ostream& out) {
     out << "found solution\n";
    //syn_net.print_all(out);
    syn_net.print_one(out);
  }

  void print_counterexample(std::ostream& out) {
  }

  bool verify() {
    boost::timer timer;
    VerifyerContext ver;
    bool success = syn_net.verify_or_add_counterexample(ver);
    time_verify += timer.elapsed();
    return success;
  }

  bool synth()
  {
    boost::timer timer;
    bool success = syn_net.synth();
    time_synth += timer.elapsed();
    return success;
  }

  result_type operator() ()
  {
    while(true) {
      while( synth() ) {
        print_solution(std::cout);
        if( verify() ) {
          std::cout << "Found Solution." << std::endl;
          print_solution(std::cout);
          return result_type();
        } else {
          print_counterexample(std::cout);
        }
      }
      std::cout << "add another level." << std::endl;
      syn_net.add_level();
    }
    return result_type();
  }

};
