#pragma once 
#include "SMT_Command_Map.hpp"
#include "../../result_wrapper.hpp"
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
        , var_map(*var_map_ptr)
      {}

      UTreeEvaluator(Context &ctx,
                     VarMap &var_map)
        : ctx(ctx)
        , var_map(var_map)
      {}

      void evaluateInstance(utree const &ast) {
        for ( utree::const_iterator it = ast.begin(), ie = ast.end();
              it != ie; ++it ) {
          evaluateCommand(*it);
        }
      }

      void evaluateCommand(utree const &ast) {
        assert( ast.size() > 0 );
        utree::const_iterator ast_it = ast.begin();
        std::string const symbol_string = utreeToString(*ast_it);
        boost::optional<Command> cmd =
          SMT_Command_Map<Context>::get_command(symbol_string, ctx, var_map);
        if ( cmd ) {
          boost::optional<boost::any> result = SMT_Command_Map<Context>::execute_command(*cmd, ast);
          if ( result ) {
            if ( symbol_string == "check-sat" ) {
              metaSMT::result_wrapper rw = boost::any_cast<metaSMT::result_wrapper>(*result);
              std::string s = rw;
              std::cerr << s << '\n';
            }
            else if ( symbol_string == "get-value" ) {
              metaSMT::result_wrapper rw = boost::any_cast<metaSMT::result_wrapper>(*result);
              std::string s = rw;
              std::cerr << s << '\n';
            }
          }
        }
        else {
          std::cerr << "ERROR: Unsupported command ``" << symbol_string << "\'\'\n";
          ::exit(-1);
        }
      }

    protected:
      Context &ctx;
      boost::shared_ptr<VarMap> var_map_ptr;
      VarMap &var_map;
    }; // UTreeEvaluator
  }// namespace evaluator
} // namespace metaSMT
