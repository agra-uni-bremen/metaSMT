#pragma once

#include "../Features.hpp"

#include <boost/mpl/assert.hpp>
#include <boost/function.hpp>

namespace metaSMT {

  struct set_symbol_table_cmd { typedef void result_type; };

  /**
   * \brief Use custom symbol table for variable naming
   *
   *
   *
   * \code
   *  DirectSolver_Context< SMT2 > ctx;
   *
   * struct Lookup {
   *   std::map<unsigned, std::string> &map_;
   * 
   *   Lookup(std::map<unsigned, std::string> &map)
   *   : map_(map) {}
   * 
   *   std::string operator()(unsigned id) {
   *     return map_[id];
   *   }
   * 
   *   void insert(predicate p, std::string const &name) {
   *     map_.insert(std::make_pair(boost::proto::value(p).id, name));
   *   }
   * };
   *
   *  
   * std::map<unsigned, std::string> symbols;
   * Lookup lookup(symbols);
   * 
   * predicate x = new_variable();
   * lookup.insert(x, "x");
   * set_symbol_table( ctx, lookup);
   *
   * \endcode
   * \ingroup API
   * \defgroup SymbolTable SymbolTable API
   * @{
   */

  /**
   * \class IgnoreSymbolTable SymbolTable.hpp metaSMT/SymbolTable.hpp
   * \brief Ignore symbol table commands
   */
  template <typename Context > 
  struct IgnoreSymbolTable : Context {
      void command ( set_symbol_table_cmd const &, boost::function<std::string(unsigned)> table) {
        /* ignored */
      }

      using Context::command;
  };

  namespace features {
    /* IgnoreSymbolTable supports symbol table (by ignoring it) */
    template<typename Context>
    struct supports< IgnoreSymbolTable<Context>, set_symbol_table_cmd>
    : boost::mpl::true_ {};

    /* Forward all other supported operations */
    template<typename Context, typename Feature>
    struct supports< IgnoreSymbolTable<Context>, Feature>
    : supports<Context, Feature>::type {};
  }

  /**
   * \brief set symbol table
   * \param ctx The context to work on
   * \param table Symbol table used to name variables
   * \return void
   * \throws Assertion at compile time if \c Context does not support symbol tables
   *
   */
  template <typename Context >
  void set_symbol_table( Context & ctx, boost::function<std::string(unsigned)> table) {
    BOOST_MPL_ASSERT_MSG(( features::supports<Context, set_symbol_table_cmd>::value ),
        context_does_not_support_symbol_table, (Context) );
    ctx.command(set_symbol_table_cmd(), table);
  }

  /**@}*/

} /* metaSMT */

