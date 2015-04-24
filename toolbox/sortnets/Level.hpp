#pragma once

#include <metaSMT/frontend/Logic.hpp>

#include <boost/multi_array.hpp>

using namespace metaSMT::logic;

struct Level {

  std::vector<predicate> vars;

  Level(unsigned size)
  {
    for (unsigned i = 0; i < size; i++) {
      vars.push_back( new_variable() );
    }
  }

  predicate & operator[] (unsigned i) {
    return vars[i];
  }

  template <typename Context>
  typename Context::result_type
  is_sorted(Context & ctx) {
    //std::cout << "is_sorted called\n";
    typename Context::result_type ret = evaluate(ctx, True);
    for (unsigned i = 1; i < vars.size(); i++) {
      ret = evaluate(ctx, And(ret,
          implies(vars[i-1], vars[i])
      ));
    }
    return ret;
  }

  template <typename Context>
  typename Context::result_type
  equal_to(Context & ctx, std::string const & val) {
    typename Context::result_type ret = evaluate(ctx, True);
    for (unsigned i = 0; i < vars.size(); i++) {
      if(val[i] == '1') {
        ret = evaluate(ctx, And(ret,
              vars[i]
              ));
      } else {
        ret = evaluate(ctx, And(ret,
              Not(vars[i])
              ));
      }
    }
    return ret;
  }

  template <typename Context>
  void print_assignment(std::ostream& out, Context & ctx) {
    for (unsigned i = 0; i < vars.size(); i++) {
      bool b = read_value(ctx, vars[i]);
      out << b;
    }
    out << '\n';
  }

  template <typename Context>
  void print(std::ostream& out, Context & ctx) {
    print_assignment(out, ctx);
  }

  template <typename Context>
  std::string assignment(Context & ctx) {
    std::string ret(vars.size(), '-');
    for (unsigned i = 0; i < vars.size(); i++) {
      bool b = read_value(ctx, vars[i]);
      ret[i] = b ? '1' : '0';
    }
    return ret;
  }
};
