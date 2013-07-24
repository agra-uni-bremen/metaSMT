#pragma once 
#include "SMT_Command_Map.hpp"
#include "../../result_wrapper.hpp"
#include "../SimpleSymbolTable.hpp"
#include <boost/spirit/include/support_utree.hpp>
#include <boost/shared_ptr.hpp>
#include <boost/optional.hpp>
#include <map>
#include <iostream>

namespace metaSMT {
  namespace evaluator {
    template<typename Context>
    struct UTreeEvaluator {
      typedef typename Context::result_type result_type;
      typedef boost::spirit::utree utree;

      typedef type::TypedSymbol<Context> TypedSymbol;
      typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
      typedef std::map<std::string, TypedSymbolPtr > VarMap;

      typedef typename SMT_Command_Map<Context>::Command Command;

      UTreeEvaluator(Context &ctx)
        : ctx(ctx)
        , var_map_ptr(new VarMap())
        , var_map(*var_map_ptr) {
        set_symbol_table(ctx, table);
      }

      UTreeEvaluator(Context &ctx,
                     VarMap &var_map)
        : ctx(ctx)
        , var_map(var_map) {
        set_symbol_table(ctx, table);
      }

      void evaluateInstance(utree const &ast) {
        for ( utree::const_iterator it = ast.begin(), ie = ast.end();
              it != ie; ++it ) {
          evaluateCommand(*it);
        }
      }

      void evaluateCommand(utree const &ast) {
        assert( ast.size() > 0 );
        utree::const_iterator ast_it = ast.begin();
        std::string const name = utreeToString(*ast_it);
        boost::optional<Command> command =
          SMT_Command_Map<Context>::get_command(name, ctx, var_map, table);
        boost::optional<boost::any> result =
          SMT_Command_Map<Context>::execute_command(*command, ast);
        if ( !command ) {
          std::cerr << "ERROR: Unsupported command ``" << name << "\'\'\n";
          ::exit(-1);
        }

        if ( result ) {
          if ( name == "check-sat" ) {
            bool const sat = boost::any_cast<bool>(*result);
            std::cout << (sat ? "sat" : "unsat") << '\n';
          }
          else if ( name == "get-value" ) {
            typedef boost::tuple<std::string, TypedSymbolPtr> VarType; 
            VarType var = boost::any_cast<VarType>(*result);
            std::string const name = boost::get<0>(var);
            TypedSymbolPtr symbol = boost::get<1>(var);
            std::string ret = "<Unknown>";
            if ( symbol->isBool() ) {
              bool const b = read_value(ctx, symbol->eval(ctx));
              std::cout << "((" + name + " " + (b ? "true" : "false") + "))" << '\n';
            }
            else if (symbol->isBitVector() ) {
              std::string const value = read_value(ctx, symbol->eval(ctx));
              std::cout << "((" + name + " #b" + value + "))" << '\n';
            }
            else {
              assert( false && "Variable type is not supported" );
            }
          }
        }
      }

    protected:
      Context &ctx;
      boost::shared_ptr<VarMap> var_map_ptr;
      VarMap &var_map;
      support::simple_symbol_table table;
    }; // UTreeEvaluator
  }// namespace evaluator
} // namespace metaSMT
