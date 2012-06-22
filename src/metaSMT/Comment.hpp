#pragma once

#include "Features.hpp"

#include <boost/mpl/assert.hpp>

namespace metaSMT {

  namespace features {
    struct comment_api {};
  } /* features */

  struct write_comment { typedef void result_type; };

  /**
   * \brief Insert comments into the instance file
   *
   *
   *
   * \code
   *  DirectSolver_Context< SMT2 > ctx;
   *  
   *  assertion(ctx, equal(True, False);
   *  comment(ctx, "now call solve");
   *  
   *  solve(ctx);
   * \endcode
   * \ingroup API
   * \defgroup Comment Comments API
   * @{
   */

  /**
   * \class IgnoreComments Comment.hpp metaSMT/Comment.hpp
   * \brief Ignore comment commands
   */
  template <typename Context > 
  struct IgnoreComments : Context {
      void command ( write_comment const &, std::string const & message) {
        /* ignored */
      }

      using Context::command;
  };

  namespace features {
    /* IgnoreComments supports comment api (by ignoring it) */
    template<typename Context>
    struct supports< IgnoreComments<Context>, features::comment_api>
    : boost::mpl::true_ {};

    /* Forward all other supported operations */
    template<typename Context, typename Feature>
    struct supports< IgnoreComments<Context>, Feature>
    : supports<Context, Feature>::type {};
  }


  /**
   * \brief write a comment
   * \param ctx The context to work on
   * \param message The comment
   * \return void
   * \throws Assertion at compile time if \c Context does not support comments
   *
   */
  template <typename Context >
  void comment( Context & ctx, std::string const &  message) {
    BOOST_MPL_ASSERT_MSG(( features::supports<Context, features::comment_api>::value ),
        context_does_not_support_comment_api, (Context) );
    ctx.command(write_comment(), message);
  }

  /**@}*/

} /* metaSMT */

