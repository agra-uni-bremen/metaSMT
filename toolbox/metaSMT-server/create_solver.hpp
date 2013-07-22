#pragma once
#include "Solver_Name_Map.hpp"
#include "SolverProcess.hpp"

namespace detail {
  struct CreateSolverBase
    : public boost::static_visitor<void> {
  public:
    CreateSolverBase(bool &found,
                     SolverBase *&solver,
                     std::string const &name)
      : found(found)
      , solver(solver)
      , name(name)
    {}

    template < typename Pair >
    void operator()( Pair const & ) {
      typedef typename Pair::first Name;
      typedef typename Pair::second BackendType;
      if ( !found && boost::mpl::c_str<Name>::value == name ) {
        solver = new Solver<BackendType>();
        found = true;
      }
    }

    bool &found;
    SolverBase *&solver;
    std::string name;
  }; // CreateSolverBase
} // detail

static SolverBase *create_solver(std::string const &name) {
  bool found = false;
  SolverBase *solver = 0;
  detail::CreateSolverBase vis(found, solver, name);
  boost::mpl::for_each<metaSMT::Solver_Name_Map>(vis);
  assert( found && "Undefined solver mapping" );
  return solver;
}
