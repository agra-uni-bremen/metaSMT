#pragma once
#include "Command.hpp"

#include <boost/spirit/include/support_utree.hpp>
#include <boost/shared_ptr.hpp>
#include <boost/mpl/map/map20.hpp>
#include <boost/mpl/string.hpp>
#include <boost/mpl/for_each.hpp>
#include <boost/optional.hpp>
#include <boost/variant.hpp>

#include <map>

namespace metaSMT {
  namespace evaluator {
    namespace mpl = boost::mpl;
    namespace spirit = boost::spirit;

    template < typename Context >
    struct SMT_Command_Map {
      typedef mpl::map11<
        mpl::pair<
          string_concat<mpl::string<'d','e','c','l','a','r','e','-'>, mpl::string<'f','u','n'> >::type
        , cmd::DeclareFun<Context>
        >
      , mpl::pair<
          string_concat<mpl::string<'g','e','t','-'>, mpl::string<'v','a','l','u','e'> >::type
        , cmd::GetValue<Context>
        >
      , mpl::pair<
          string_concat<mpl::string<'s','e','t','-'>, mpl::string<'l','o','g','i','c'> >::type
        , cmd::SetLogic<Context>
        >
      , mpl::pair<
          string_concat<mpl::string<'s','e','t','-'>, mpl::string<'i','n','f','o'> >::type
        , cmd::SetInfo<Context>
        >
      , mpl::pair<
          string_concat<mpl::string<'s','e','t','-'>, mpl::string<'o','p','t','i','o','n'> >::type
        , cmd::SetOption<Context>
        >
      , mpl::pair<
          string_concat<mpl::string<'g','e','t','-'>, mpl::string<'o','p','t','i','o','n'> >::type
        , cmd::GetOption<Context>
        >
      , mpl::pair<
          string_concat<mpl::string<'c','h','e','c','k','-'>, mpl::string<'s','a','t'> >::type
        , cmd::CheckSat<Context>
        >
      , mpl::pair<mpl::string<'p','u','s','h'>, cmd::Push<Context> >
      , mpl::pair<mpl::string<'p','o','p'>, cmd::Pop<Context> >
      , mpl::pair<mpl::string<'e','x','i','t'>, cmd::Exit<Context> >
      , mpl::pair<mpl::string<'a','s','s','e','r','t'>, cmd::Assert<Context> >
      > TheMapping;

      typedef boost::variant<
        cmd::DefaultConstructableDummyCommand
      , cmd::DeclareFun<Context>
      , cmd::GetValue<Context>
      , cmd::SetLogic<Context>
      , cmd::SetInfo<Context>
      , cmd::SetOption<Context>
      , cmd::GetOption<Context>
      , cmd::CheckSat<Context>
      , cmd::Push<Context>
      , cmd::Pop<Context>
      , cmd::Exit<Context>
      , cmd::Assert<Context>
      > Command;

      typedef type::TypedSymbol<Context> TypedSymbol;
      typedef boost::shared_ptr<TypedSymbol> TypedSymbolPtr;
      typedef std::map<std::string, TypedSymbolPtr> VarMap;
      typedef spirit::utree utree;

      class RunCommandVisitor
        : public boost::static_visitor< boost::optional<boost::any> > {
      public:
        RunCommandVisitor(utree const &ast)
          : ast(ast)
        {}

        template < typename Command >
        typename boost::enable_if<
          typename boost::is_same<typename Command::result_type, void>::type
          , boost::optional<boost::any>
        >::type
        operator()(Command command) const {
          command(boost::optional<utree>(ast));
          return boost::optional<boost::any>();
        }

        template < typename Command >
        typename boost::disable_if<
          typename boost::is_same<typename Command::result_type, void>::type
        , boost::optional<boost::any>
        >::type
        operator()(Command command) const {
          return  boost::optional<boost::any>(command(boost::optional<utree>(ast)));
        }

        utree const ast;
      }; // RunCommandVisitor

      struct GetCommandVisitor {
      public:
        GetCommandVisitor(bool &found,
                          Command &command,
                          std::string const &name,
                          Context &ctx,
                          VarMap &var_map,
                          support::simple_symbol_table &table)
          : found(found)
          , command(command)
          , name(name)
          , ctx(ctx)
          , var_map(var_map)
          , table(table)
        {}

        template < typename Pair >
        void operator()( Pair const & ) {
          typedef typename Pair::first String;
          typedef typename Pair::second Cmd;

          if ( !found &&
               mpl::c_str<String>::value == name ) {
            found = true;
            command = Cmd(&ctx, &var_map, &table);
          }
        }

        bool &found;
        Command &command;
        std::string name;
        Context &ctx;
        VarMap &var_map;
        support::simple_symbol_table &table;
      }; // GetCommandVisitor

      static boost::optional<boost::any>
      execute_command(Command const &command, utree const &ast) {
        return boost::apply_visitor(RunCommandVisitor(ast), command);
      }

      static boost::optional<Command>
      get_command(std::string const &name, Context &ctx, VarMap &var_map,
                  support::simple_symbol_table &table) {
        bool found = false;
        Command command;
        GetCommandVisitor vis(found, command, name, ctx, var_map, table);
        mpl::for_each<TheMapping>(vis);
        if (found) {
          return boost::optional<Command>(command);
        }
        else {
          return boost::optional<Command>();
        }
      }      
    }; // SMT_Command_Map
  } // evaluator
} // metaSMT
