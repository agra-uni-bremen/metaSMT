#ifndef SOLVERS_HPP
#define SOLVERS_HPP

#include <metaSMT/support/default_visitation_unrolling_limit.hpp>
#include <metaSMT/expression/expression.hpp>

#include <metaSMT/support/disable_warnings.hpp>
#include <boost/variant.hpp>
#include <boost/proto/core.hpp>
#include <metaSMT/support/enable_warnings.hpp>

namespace proto = boost::proto;

#include "python_config.hxx"

#include <metaSMT/backend/ClauseWriter.hpp>
#if ENABLE_SOLVER_AIGER
#include <metaSMT/backend/SAT_Aiger.hpp>
#endif
#include <metaSMT/backend/SAT_Clause.hpp>
#include <metaSMT/backend/SMT2.hpp>

//#include <metaSMT/GraphSolver_Context.hpp>
#include <metaSMT/BitBlast.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/UnpackFuture_Context.hpp>
#include <metaSMT/Priority_Context.hpp>

// define all solvers
#if ENABLE_SOLVER_SWORD
#include <metaSMT/backend/SWORD_Backend.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::solver::SWORD_Backend> sword_solver;
#endif

#if ENABLE_SOLVER_BOOLECTOR
#include <metaSMT/backend/Boolector.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::solver::Boolector> boolector_solver;
#endif

#if ENABLE_SOLVER_Z3
#include <metaSMT/backend/Z3_Backend.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::solver::Z3_Backend> z3_solver;
#endif

#if ENABLE_SOLVER_CUDD
#include <metaSMT/backend/CUDD_Distributed.hpp>
// defined by CUDD
#undef CONST
typedef metaSMT::DirectSolver_Context<metaSMT::BitBlast<metaSMT::solver::CUDD_Distributed> > cudd_solver;
#endif

#if ENABLE_SOLVER_MINISAT
#include <metaSMT/backend/MiniSAT.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::BitBlast<metaSMT::SAT_Clause<metaSMT::solver::MiniSAT> > > minisat_solver;
#if ENABLE_SOLVER_AIGER
typedef metaSMT::DirectSolver_Context<metaSMT::BitBlast<metaSMT::SAT_Aiger<metaSMT::solver::MiniSAT> > > minisat_aiger_solver;
#endif
#endif

#if ENABLE_SOLVER_PICOSAT
#include <metaSMT/backend/PicoSAT.hpp>
typedef metaSMT::DirectSolver_Context<metaSMT::BitBlast<metaSMT::SAT_Clause<metaSMT::solver::PicoSAT> > > picosat_solver;
#endif

typedef metaSMT::DirectSolver_Context<metaSMT::BitBlast<metaSMT::SAT_Clause<metaSMT::solver::ClauseWriter<metaSMT::solver::dimacs_solver<metaSMT::solver::executable::Glucoser> > > > > glucoser_executable_solver;
typedef metaSMT::DirectSolver_Context<metaSMT::BitBlast<metaSMT::SAT_Clause<metaSMT::solver::ClauseWriter<metaSMT::solver::dimacs_solver<metaSMT::solver::executable::MiniSAT> > > > > minisat_executable_solver;
typedef metaSMT::DirectSolver_Context<metaSMT::BitBlast<metaSMT::SAT_Clause<metaSMT::solver::ClauseWriter<metaSMT::solver::dimacs_solver<metaSMT::solver::executable::PicoSAT> > > > > picosat_executable_solver;
typedef metaSMT::DirectSolver_Context<metaSMT::BitBlast<metaSMT::SAT_Clause<metaSMT::solver::ClauseWriter<metaSMT::solver::dimacs_solver<metaSMT::solver::executable::Plingeling> > > > > plingeling_executable_solver;
typedef metaSMT::DirectSolver_Context<metaSMT::BitBlast<metaSMT::SAT_Clause<metaSMT::solver::ClauseWriter<metaSMT::solver::dimacs_solver<metaSMT::solver::executable::PrecoSAT> > > > > precosat_executable_solver;

typedef metaSMT::DirectSolver_Context<metaSMT::solver::SMT2> smt2_solver;

#if ENABLE_SOLVER_CONSTRAINT
/**
 * Define a multi-threaded, prioritized solver.
 *
 * It is mainly useful for a situation where many solutions need to be
 * generated for a single constraint. In the best case the constraint
 * is build up once and unchanged later.
 *
 */
typedef
  metaSMT::DirectSolver_Context< metaSMT::UnpackFuture_Context<
    metaSMT::solver::Z3_Backend
  > > z3_constraint_solver;
typedef
  metaSMT::DirectSolver_Context< metaSMT::UnpackFuture_Context<
    metaSMT::BitBlast<metaSMT::solver::CUDD_Distributed >
  > > cudd_constraint_solver;
typedef metaSMT::Priority_Context<
    cudd_constraint_solver, // if the first one finishes it will be used
    z3_constraint_solver // until then, use this one.
    > constraint_solver;
#endif

//typedef metaSMT::GraphSolver_Context<metaSMT::solver::Boolector> boolector_graph_solver;

typedef boost::mpl::pop_back<boost::mpl::vector<
#if ENABLE_SOLVER_SWORD
  boost::shared_ptr<sword_solver>,
#endif
#if ENABLE_SOLVER_BOOLECTOR
  boost::shared_ptr<boolector_solver>,
#endif
//  boost::shared_ptr<boolector_graph_solver>,
#if ENABLE_SOLVER_Z3
  boost::shared_ptr<z3_solver>,
#endif
#if ENABLE_SOLVER_Z3_EXECUTABLE
  boost::shared_ptr<smt2_solver>,
#endif
#if ENABLE_SOLVER_CUDD
  boost::shared_ptr<cudd_solver>,
#endif
#if ENABLE_SOLVER_MINISAT
  boost::shared_ptr<minisat_solver>,
#if ENABLE_SOLVER_AIGER
  boost::shared_ptr<minisat_aiger_solver>,
#endif //// AIGER
#endif // MiniSAT

#if ENABLE_SOLVER_PICOSAT
  boost::shared_ptr<picosat_solver>,
#endif
#if ENABLE_SOLVER_GLUCOSER
  boost::shared_ptr<glucoser_executable_solver>,
#endif
#if ENABLE_SOLVER_MINISAT_EXECUTABLE
  boost::shared_ptr<minisat_executable_solver>,
#endif
#if ENABLE_SOLVER_PICOSAT_EXECUTABLE
  boost::shared_ptr<picosat_executable_solver>,
#endif
#if ENABLE_SOLVER_PLINGELING_EXECUTABLE
  boost::shared_ptr<plingeling_executable_solver>,
#endif
#if ENABLE_SOLVER_PRECOSAT_EXECUTABLE
  boost::shared_ptr<precosat_executable_solver>,
#endif
#if ENABLE_SOLVER_CONSTRAINT
  boost::shared_ptr<constraint_solver>,
#endif
  boost::mpl::void_
> >::type solver_types;


typedef boost::make_variant_over< solver_types >::type solver;

void export_solvers();


#endif /* SOLVERS_HPP */
