#pragma once
#include "SolverProcess.hpp"
#include <metaSMT/support/parser/SMT2Parser.hpp>
#include <metaSMT/support/parser/UTreeEvaluator.hpp>
#include <metaSMT/support/parser/UTreeToString.hpp>
#include <metaSMT/support/SimpleSymbolTable.hpp>
#include <boost/shared_ptr.hpp>
#include <boost/optional.hpp>
#include <sstream>
#include <string>

namespace eval = metaSMT::evaluator;
namespace spirit = boost::spirit;

template < typename Context >
class Solver : public SolverBase {
public:
  typedef typename eval::UTreeEvaluator<Context> Evaluator;
  typedef metaSMT::type::TypedSymbol<Context> TypedSymbol;
  typedef boost::shared_ptr<TypedSymbol> TypedSymbolPtr;
  typedef std::map<std::string, TypedSymbolPtr> VarMap;

  typedef typename eval::SMT_Command_Map<Context>::Command Command;

  Solver()
    : evaluator(solver, var_map)
    , parser(evaluator)
  {}

  void start() {
    std::cerr << "START" << '\n';
    for (;;) {
      std::string ret = SolverBase::success;
      std::string s = sp->child_read_command();
      // std::cerr << "[SOLVER] " << s << '\n';

      try {
        spirit::utree::list_type const list = parse(s);

        for ( spirit::utree::const_iterator it = list.begin(), ie = list.end();
                it != ie; ++it ) {
          spirit::utree const ast = *it;
          assert( ast.size() > 0 );

          std::string const command = eval::utreeToString(*ast.begin());
          // std::cerr << "COMMAND: " << command << '\n';

          boost::optional<Command> cmd =
          eval::SMT_Command_Map<Context>::get_command(command, solver, var_map, table);
          if ( !cmd )
            throw std::invalid_argument( "Unsupported command" );
          boost::optional<boost::any> result =
          eval::SMT_Command_Map<Context>::execute_command(*cmd, ast);
          if ( result ) {
            ret = makeResultString(command, *result);
          }
        }
      } 
      catch (std::invalid_argument e) {
        std::cerr << "[SOLVER] " << e.what() << std::endl;
        ret = "error";
      }
      catch (std::exception e) {
        std::cerr << "[SOLVER] " << e.what() << std::endl;
        ret = "error";
      }
      // std::cerr << "[SOLVER] CHILD WRITE COMMAND: " << ret << '\n';
      sp->child_write_command(ret);
    }
  }

private:
  spirit::utree::list_type parse(std::string const &s) {
    std::stringstream ss(s);
    spirit::utree::list_type list;
    bool const success = parser.parse(ss, list);
    // std::cerr << "[SOLVER] SUCCESS = " << success << '\n';
    if ( !success ) {
      throw std::invalid_argument( "Unsupported syntax" );
    }
    return list;
  }

  std::string makeCheckSatResult(boost::any const &result) {
    bool const sat = boost::any_cast<bool>(result);
    //std::cerr << "[SOLVER] check-sat = " << sat << '\n';
    return (sat ? "sat" : "unsat");
  }

  std::string makeGetValueResult(boost::any const &result) {
    typedef boost::tuple<std::string,TypedSymbolPtr> var_type;
    var_type var = boost::any_cast<var_type>(result);
    std::string const name = boost::get<0>(var);
    TypedSymbolPtr const symbol = boost::get<1>(var);
    std::string ret = "<Unknown>";
    if ( symbol->isBool() ) {
      bool const b = read_value(solver, symbol->eval(solver));
      ret = "((" + name + " " + (b ? "true" : "false") + "))";
    }
    else if (symbol->isBitVector() ) {
      std::string const value = read_value(solver, symbol->eval(solver));
      ret = "((" + name + " #b" + value + "))";
    }
    else {
      assert( false && "Variable type is not supported" );
    }
    //std::cerr << "[SOLVER] get-value = " << ret << '\n';
    return ret;
  }

  std::string makeResultString(std::string const &name,
                               boost::any const &result) {
    if ( name == "check-sat" ) {
      return makeCheckSatResult(result);
    }
    else if ( name == "get-value" ) {
      return makeGetValueResult(result);
    }
    assert( false && "Command has no result" );
    return "<Unknown>";
  }

  Context solver;
  VarMap var_map;
  Evaluator evaluator;
  metaSMT::smt2::SMT2Parser<Evaluator> parser;
  metaSMT::support::simple_symbol_table table;
}; // Solver
