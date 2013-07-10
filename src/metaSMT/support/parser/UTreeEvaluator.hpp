#pragma once 
#include "Command.hpp"

#include "../../tags/QF_BV.hpp"
#include "../../result_wrapper.hpp"
#include "../../API/Stack.hpp"
#include "../../io/SMT2_ResultParser.hpp"
#include "../../support/SMT_Tag_Mapping.hpp"

#include <boost/spirit/include/support_utree.hpp>
#include <boost/shared_ptr.hpp>
#include <boost/optional.hpp>
#include <boost/mpl/string.hpp>
#include <boost/mpl/for_each.hpp>
#include <boost/mpl/not.hpp>

#include <iostream>
#include <map>
#include <stack>
#include <list>

namespace metaSMT {
  namespace evaluator {
    namespace QF_BV = metaSMT::logic::QF_BV;
    namespace mpl = boost::mpl;

    template<typename Context>
    struct UTreeEvaluator {
      typedef typename Context::result_type result_type;
      typedef boost::spirit::utree utree;
      
      typedef boost::function<void(boost::optional<utree>)> CommandPointer;
      typedef std::map<std::string, CommandPointer> CommandMap;

      typedef type::TypedSymbol<Context> TypedSymbol;
      typedef boost::shared_ptr< TypedSymbol > TypedSymbolPtr;
      typedef std::map<std::string, TypedSymbolPtr > VarMap;

    UTreeEvaluator(Context &ctx)
      : ctx(ctx)
      , var_map_ptr(new VarMap())
      , var_map(*var_map_ptr) {
      initialize();
    }

      UTreeEvaluator(Context &ctx,
                     VarMap &var_map)
        : ctx(ctx)
        , var_map(var_map) {
        initialize();
      }

      void initialize() {
        command_map["set-logic"] =   cmd::SetLogic<Context>(ctx);
        command_map["set-info"] =    cmd::SetInfo<Context>(ctx);
        command_map["set-option"] =  cmd::SetOption<Context>(ctx);
        command_map["get-option"] =  cmd::GetOption<Context>(ctx);
        command_map["check-sat"] =   cmd::CheckSat<Context>(ctx);
        command_map["assert"] =      cmd::Assert<Context>(ctx, var_map);
        command_map["declare-fun"] = cmd::DeclareFun<Context>(ctx, var_map);
        command_map["get-value"] =   cmd::GetValue<Context>(ctx, var_map);
        command_map["push"] =        cmd::Push<Context>(ctx);
        command_map["pop"] =         cmd::Pop<Context>(ctx);
        command_map["exit"] =        cmd::Exit<Context>(ctx);
      }
      
      result_type evaluateInstance(utree ast) {
        for ( utree::iterator it = ast.begin(), ie = ast.end(); it != ie; ++it ) {
          utree command  = *it;
          evaluateCommand(command);
        }
      }

      void evaluateCommand(utree command) {
        assert( command.size() > 0 );
        utree::iterator cmd_it = command.begin();
        std::string const symbol_string = utreeToString(*cmd_it);
        CommandMap::const_iterator it = command_map.find(symbol_string);
        if ( it != command_map.end() ) {
          it->second( boost::optional<utree>(command) );
        }
        else {
          std::cerr << "ERROR: Unsupported command ``" << symbol_string << "\'\'\n";
          ::exit(-1);
        }
      }

    protected:
      Context &ctx;
      CommandMap command_map;

      boost::shared_ptr<VarMap> var_map_ptr;
      VarMap &var_map;
    }; // UTreeEvaluator
  }// namespace evaluator
} // namespace metaSMT
