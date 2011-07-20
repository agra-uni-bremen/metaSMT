#pragma once

#include "Features.hpp"

#include <boost/any.hpp>
#include <boost/proto/core.hpp>
#include <boost/proto/context.hpp>
#include <boost/thread/future.hpp>

namespace metaSMT {

  /**
   * @brief direct Solver integration
   *
   *  DirectSolver_Context takes a SolverType and directly feeds all commands
   *  to it. Variable expressions are cached and only evaluated once.
   **/
  template<typename SolverContext>
  struct UnpackFuture_Context 
    : SolverContext
  { 
    UnpackFuture_Context() {}

    /// The returned expression type is the result_type of the SolverContext
    typedef typename SolverContext::result_type result_type;

    template< typename T>
    result_type operator() (boost::shared_future<T> & e, boost::any const & any) {
      return e.get();
    }

    using SolverContext::command;
    using SolverContext::operator();

  };

  namespace features {
    template<typename Context, typename Feature>
    struct supports< UnpackFuture_Context<Context>, Feature>
    : supports<Context, Feature>::type {};
  }


} // namespace metaSMT 

//  vim: ft=cpp:ts=2:sw=2:expandtab
