#pragma once

#include "../impl/_var_id.hpp"
#include "../tags/Logic.hpp"
#include "../Features.hpp"

#include <cstdio>
#include <vector>
#include <list>

#include <boost/any.hpp>
#include <boost/foreach.hpp>
#include <boost/tr1/unordered_map.hpp>
#include <boost/mpl/assert.hpp>

namespace metaSMT {

  namespace features {
    struct stack_api {};
  } /* features */

  struct stack_push { typedef void result_type; };
  struct stack_pop { typedef void result_type; };

  /**
   * \brief push and pop over assertions.
   *
   * Stack provides the ability to use SMT2-like push and pop operations.
   * 
   * For solvers without native support for stack operations push and pop can
   * be emulated by using assumptions with Stack_emulation.
   * However to ensure the availability of push and pop the context can be wrapped
   * in Stack which will do the right thing.
   * \code
   *  // ensure ctx supports push/pop
   *  DirectSolver_Context<Stack<Context> > ctx;
   *  
   *  // add a stack level
   *  push(ctx);
   *  // add assertions and solve
   *  assertion( equal(True, False);
   *  
   *  solve(ctx);
   *  // UNSAT, remove this stack level again
   *  pop(ctx);
   * \endcode
   * \ingroup API
   * \defgroup Stack Assertion Stack API
   * @{
   */

  template<typename Context>
  struct Stack_emulation : public Context
  {
    typedef typename Context::result_type result_type;

    void assertion ( result_type const& e )
    {
      if ( stack_.empty() ) {
        Context::assertion( e );
      } else {
        stack_.back().push_back( e );
      }
    }

    bool solve ( )
    {
      BOOST_FOREACH ( stack_level const & se, stack_)
      {
        BOOST_FOREACH( result_type const & r, se)
        {
          Context::assumption ( r );
        }
      }
      return Context::solve () ;
    }

    void command ( stack_push const &, unsigned howmany) {
      while (howmany > 0) {
        stack_.push_back( stack_level() );
        --howmany;
      }
    }

    void command ( stack_pop const &, unsigned howmany) {
      while (howmany > 0) {
        stack_.pop_back();
        --howmany;
      }
    }

    using Context::command;


    private:
      typedef std::list<result_type> stack_level;
      std::vector< stack_level> stack_;

  };


  template< typename Context >
  struct Stack
  : boost::mpl::if_< features::supports< Context, features::stack_api>
    , Context
    , Stack_emulation< Context >
  >::type {};

  namespace features {
    /* Stack supports stack api */
    template<typename Context>
    struct supports< Stack<Context>, features::stack_api>
    : boost::mpl::true_ {};

    /* Forward all other supported operations */
    template<typename Context, typename Feature>
    struct supports< Stack<Context>, Feature>
    : supports<Context, Feature>::type {};
  }

  /**
   * \brief assertion stack push function
   * \param ctx The context to work on
   * \param howmany number of stack leves to push, defaults to 1
   * \return void
   *
   */
  template <typename Context >
  typename boost::enable_if< features::supports<Context, features::stack_api> >::type
  push( Context & ctx, unsigned howmany=1) {
    ctx.command(stack_push(), howmany);
  }

  /**
   * \brief assertion stack pop function
   * \param ctx The context to work on
   * \param howmany number of stack leves to pop, defaults to 1
   * \return void
   *
   */
  template <typename Context >
  typename boost::enable_if< features::supports<Context, features::stack_api> >::type
  pop( Context & ctx, unsigned howmany=1) {
    ctx.command(stack_pop(), howmany);
  }

  /** \cond */
  /* error if unsupported **/
  template <typename Context >
  typename boost::disable_if< features::supports<Context, features::stack_api> >::type
  push( Context & ctx, unsigned howmany=1) {
    BOOST_MPL_ASSERT_MSG(( features::supports<Context, features::stack_api>::value ),
        context_does_not_support_push_stack_api, );
  }

  template <typename Context >
  typename boost::disable_if< features::supports<Context, features::stack_api> >::type
  pop( Context & ctx, unsigned howmany=1 ) {
    BOOST_MPL_ASSERT_MSG(( features::supports<Context, features::stack_api>::value ),
        context_does_not_support_pop_stack_api, (Context) );
  }
  /** \endcond */

  /**@}*/

} /* metaSMT */

