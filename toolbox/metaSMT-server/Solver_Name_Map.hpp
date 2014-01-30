#pragma once
#include <boost/lexical_cast.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/API/Group.hpp>
#include <metaSMT/BitBlast.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/backend/SAT_Clause.hpp>
#include <metaSMT/backend/PicoSAT.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>
#include <metaSMT/backend/SMT2.hpp>
#include <metaSMT/backend/STP.hpp>
#include <metaSMT/backend/SWORD_Backend.hpp>
#include <metaSMT/backend/MiniSAT.hpp>
#include <metaSMT/backend/CUDD_Context.hpp>
#include <boost/mpl/map.hpp>
#include <boost/mpl/string.hpp>
#include <boost/mpl/for_each.hpp>

namespace metaSMT {
  typedef boost::mpl::map<
    mpl::pair<
      string_concat< mpl::string<'B','o','o','l'>, mpl::string<'e','c','t','o','r'> >::type
    , DirectSolver_Context< IgnoreSymbolTable< Stack<solver::Boolector> > >
    >
  , mpl::pair<
      mpl::string<'C', 'U', 'D', 'D'>
    , DirectSolver_Context< IgnoreSymbolTable< Stack< Group < solver::CUDD_Context > > > >
    >
  , mpl::pair<
      mpl::string<'M','i','n','i', 'S', 'A', 'T'>
    , DirectSolver_Context< IgnoreSymbolTable< Stack< Group < BitBlast < SAT_Clause < solver::MiniSAT > > > > > >
    >
  , mpl::pair<
      mpl::string<'P','i','c','o', 'S', 'A', 'T'>
    , DirectSolver_Context< IgnoreSymbolTable< Stack< Group<BitBlast < SAT_Clause < solver::PicoSAT > > > > > >
    >
  , mpl::pair<
      mpl::string<'S','M','T','2'>
    , DirectSolver_Context< solver::SMT2 >
    >
  , mpl::pair<
      mpl::string<'S','T','P'>
    , DirectSolver_Context< IgnoreSymbolTable<Stack<solver::STP> > >
    >
  , mpl::pair<
      mpl::string<'S','W','O','R', 'D'>
    , DirectSolver_Context< IgnoreSymbolTable< Stack<solver::SWORD_Backend> > >
    >
  , mpl::pair<
      mpl::string<'Z','3'>
    , DirectSolver_Context< IgnoreSymbolTable< solver::Z3_Backend> >
    >
  > Solver_Name_Map;

  namespace detail {
    struct GetAvailableSolvers
      : public boost::static_visitor<void> {
    public:
      GetAvailableSolvers(std::string &s)
        : s(s)
      {}

      template < typename Pair >
      void operator()( Pair const & ) {
        typedef typename Pair::first Name;
        s += std::string(mpl::c_str<Name>::value) + ';';
      }

      std::string &s;
    }; // GetAvailableSolvers

    struct IsSolverAvailable
      : public boost::static_visitor<void> {
    public:
      IsSolverAvailable(bool &found,
                        std::string const &name)
        : found(found)
        , name(name)
      {}

      template < typename Pair >
      void operator()( Pair const & ) {
        typedef typename Pair::first Name;
        if ( !found && mpl::c_str<Name>::value == name) {
          found = true;
        }
      }

      bool &found;
      std::string name;
    }; // IsSolverAvailable
  } // detail

  static std::string getAvailableSolversString() {
    std::string s;
    detail::GetAvailableSolvers vis(s);
    mpl::for_each<Solver_Name_Map>(vis);
    if ( s == "" ) {
      s = "no";
    }
    return s;
  }

  static bool isSolverAvailable(std::string const &name) {
    bool found = false;
    detail::IsSolverAvailable vis(found, name);
    mpl::for_each<Solver_Name_Map>(vis);
    return found;
  }
}
