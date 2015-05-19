#pragma once

#include <metaSMT/API/Assertion.hpp>
#include <metaSMT/support/cardinality.hpp>

#include <boost/foreach.hpp>
#include <boost/timer.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>
#include <boost/tuple/tuple_io.hpp>

#include <iostream>

using namespace metaSMT;
using namespace metaSMT::logic;

template <typename Context>
struct SynthNet
{
  Context ctx;

  typedef boost::multi_array<Level*, 2> NetType;
  typedef boost::tuple<unsigned, unsigned> Tuple;
  typedef std::vector<Tuple> ExchangeGates;
  typedef std::map<Tuple, predicate> ExchangeIndex;
  typedef std::vector<ExchangeIndex> GateVariables;

  unsigned num_lines, num_levels, num_cex;
  NetType net;
  NetType::extent_gen extents;
  GateVariables gate_vars;
  ExchangeGates all_gates;


  SynthNet(unsigned lines)
  : num_lines(lines)
  , num_levels(1)
  , num_cex(0)
  {
    for (unsigned i = 0; i < lines; i++) {
      for (unsigned j = 0; j < lines; j++) {
        if (i<j) {
          all_gates.push_back(Tuple (i,j));
        }
      }
    }
    add_level_vars();
  }

  ~SynthNet() {
    // TODO: delete Levels
  }


  // add sortnet for counterexample
  //
  // 1 \/ x --\  /--y
  // 0 /\ x \/.\/...y ...
  // 1 \/ x /\./\...y
  // 0 /\ x --/  \--y
  //
  void add_counterexample( std::string const & cex) {
    //assert(num_cex < 5);

    unsigned ncx = num_cex;
    ++num_cex;
    net.resize(extents[num_cex][num_levels]);
    for (unsigned i = 0; i < num_levels; i++) {
      //std::cout << "creating CEX " << ncx << "," << i << "\n";
      net[ncx][i] = new Level(num_lines);
      if( i!=0 ) {
        connect(ncx, i-1, i);
      } else {
        comment(ctx, "equal to cex");
        metaSMT::assertion(ctx,
          net[ncx][i]->equal_to(ctx, cex)
        );
      }
    }
  }

  void add_level( ) {
    add_level_vars();
    unsigned nlv = num_levels;
    ++num_levels;
    std::cout << "adding level to " << num_cex << " " << num_levels << std::endl;
    net.resize(extents[num_cex][num_levels]);
    for (unsigned i = 0; i < num_cex; i++) {
      //std::cout << "creating Level " << i << "," << nlv << "\n";
      net[i][nlv] = new Level (num_lines);
      connect(i, nlv-1, nlv);
    }
  }

  void assumeSorted() {
    for (unsigned i = 0; i < num_cex; i++) {
      assumption(ctx,
        net[i][num_levels-1]->is_sorted(ctx)
      );
    }
  }

  void connect(unsigned ncx, unsigned aidx, unsigned bidx) {
    assert(aidx == bidx-1);
    std::vector< typename Context::result_type > ops(num_lines);
    Level & a = *net[ncx][aidx];
    Level & b = *net[ncx][bidx];
    for (unsigned i = 0; i < num_lines; i++) {
      ops[i] = evaluate(ctx, equal(a[i], b[i]));
    }

    BOOST_FOREACH (Tuple const & pos, all_gates) {
      predicate & swap = gate_vars[aidx][pos];
      unsigned p1 = pos.get<0>();
      unsigned p2 = pos.get<1>();
      comment(ctx, "exchange gate");
      assertion(ctx, implies(swap, And(
        equal(b[p1], And(a[p1],a[p2])),
        equal(b[p2],  Or(a[p1],a[p2]))
      )));
      ops[p1] = evaluate(ctx, Or(ops[p1], swap));
      ops[p2] = evaluate(ctx, Or(ops[p2], swap));
    }
    for (unsigned i = 0; i < num_lines; i++) {
      comment(ctx, "equal or exchange");
      metaSMT::assertion(ctx, ops[i]);
    }
  }

  void add_level_vars() {
    ExchangeIndex ei;
    std::vector<predicate> vars;
    BOOST_FOREACH (Tuple & tup, all_gates) {
      predicate p = new_variable();
      ei.insert(std::make_pair(tup, p));
      vars.push_back(p);
    }
    gate_vars.push_back(ei);
    comment(ctx, "swap cardinality");
    metaSMT::assertion(ctx, cardinality_leq(ctx, vars, num_lines/2u));
  }

  bool synth() {
    std::cout
      << "starting synthesis for depth " << num_levels-1
      << ", " << num_cex << " counterexamples" << std::endl;
    boost::timer timer;
    assumeSorted();
    bool b = solve(ctx);
    std::cout << "synthesis took " << timer.elapsed() << " seconds" << std::endl;
    return b;
  }


  ExchangeGates gates(unsigned level) {
    ExchangeIndex & ei = gate_vars[level];
    ExchangeGates ret;
    for( ExchangeIndex::iterator i = ei.begin();
         i != ei.end(); ++i)
    {
      bool b = read_value(ctx, i->second);
      if( b ) {
        ret.push_back( i->first );
      }
    }
    return ret;
  }

  template <typename VerifyerContext>
  bool verify_or_add_counterexample(VerifyerContext& ver) {
    boost::timer timer;
    assert(num_cex != 0);

    // build the sorting network
    for (unsigned lev = 1; lev < num_levels; lev++) {
      std::vector<bool> unused(num_lines, true);
      Level& a = *net[0][lev-1];
      Level& b = *net[0][lev];
      BOOST_FOREACH (Tuple const & exg, gates(lev-1)) {
        //std::cout << "creating gate " << lev <<" " << exg << '\n';
        unsigned p1 = exg.get<0>();
        unsigned p2 = exg.get<1>();
        //std::cout << "-- " << p1 <<" " << p2 << '\n';
        assertion(ver, And(
          equal(b[p1], And(a[p1], a[p2])),
          equal(b[p2],  Or(a[p1], a[p2]))
        ));
        unused[p1]=false;
        unused[p2]=false;
      }
      for (unsigned i = 0; i < num_lines; i++) {
        if(unused[i]) {
          //std::cout << "creating equal " << lev << " " << i << '\n';
          assertion(ver, equal(a[i],b[i]));
        }
      }
    }
    assertion(ver, Not(net[0][num_levels-1]->is_sorted(ver)));
    assertion(ver, Not(net[0][0]->is_sorted(ver)));

    bool cex_exists = solve(ver);
    std::cout << "verification took " << timer.elapsed() << " seconds" << std::endl;
    if(cex_exists) {
      Level& lev = *net[0][0];
      std::string cex = lev.assignment(ver);
      add_counterexample(cex);
      std::cout
        << "found counterexample " << num_cex << '\n'
        << cex
        << '\n'
        ;
      for (unsigned i = 1; i < num_levels; i++) {
        std::cout << net[0][num_levels-1]->assignment(ver) << '\n';
      }
    }

    return !cex_exists;
  }

  void print_all(std::ostream& out ) {
    for (unsigned i = 0; i < num_cex; i++) {
      print_one(out,i);
      out << "----\n";
    }
  }

  void print_one(std::ostream& out, unsigned cex=std::numeric_limits<unsigned>::max()) {
    if(cex >= num_cex) cex = num_cex-1;

    for (unsigned i = 0; i < num_levels; i++) {
      net[cex][i]->print_assignment(out, ctx);

      if (i == num_levels -1) {
        break; // do not print the last gates, they are not used.
      }

      ExchangeIndex & ei = gate_vars[i];

      for( ExchangeIndex::iterator i = ei.begin();
          i != ei.end(); ++i)
      {
        bool b = read_value(ctx, i->second);
        if( b ) {
          out << i->first << " ";
        }
      }
      out << '\n';
    }
  }

};
