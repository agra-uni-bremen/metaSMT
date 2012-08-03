#pragma once

#include "result_wrapper.hpp"
#include "frontend/Logic.hpp"
#include "frontend/QF_BV.hpp"
#include "Features.hpp"
#include "API/Assertion.hpp"
#include "API/Assumption.hpp"
#include "API/Options.hpp"
#include "concurrent/Threaded_Worker.hpp"
#include "support/lazy.hpp"
#include "support/protofy.hpp"

#include <boost/tuple/tuple.hpp> 
#include <boost/tuple/tuple_io.hpp> 
#include <boost/function.hpp>
#include <boost/bind.hpp>
#include <boost/thread/thread.hpp>
#include <boost/thread/future.hpp>
#include <boost/any.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/proto/core.hpp>
#include <boost/proto/context.hpp>
#include <boost/tr1/unordered_map.hpp>
#include <boost/fusion/sequence/io.hpp>
#include <boost/fusion/sequence/intrinsic/at.hpp>

#include <vector>
#include <iostream>

namespace metaSMT {

  /**
   * @brief Run two solver contexts in two threads and dispatch all calls
   * (assertions/assumptions,commands) to both of them. The "faster" solver
   * context is used to return the results and acquire variable assignments
   * assignment.
   * 
   * \tparam SolverContext1 a metaSMT context to be instanciated as the first thread (e.g. DirectSolvers_Context<...>)
   * \tparam SolverContext2 another valid metaSMT context for the second thread
   *
   * \tparam  WaitForJoin Boolean value, wait for both threeads to finish 
   *          in the destructor of Threaded_Context? (default: no)
   **/
  template<typename SolverContext1, typename SolverContext2, bool WaitForJoin=false>
  struct Threaded_Context 
    : boost::proto::callable_context< Threaded_Context<SolverContext1, SolverContext2>, boost::proto::null_context >
  { 
    Threaded_Context()
    : ctx1(new SolverContext1)
    , ctx2(new SolverContext2)
    , worker1(ctx1)
    , worker2(ctx2)
    , thread1(worker1)
    , thread2(worker2)
    , lastSAT(0)
    {}

    /**
     * \brief controls the running threads
     *
     * The destructor regulates the threads by interrupting and joining 
     * the threads.
     *
     *
     */
    ~Threaded_Context() {
      thread1.interrupt();
      thread2.interrupt();
      if(WaitForJoin) {
        thread1.join();
        thread2.join();
      }
    }

    /** \cond */
    template<typename Result>
    struct PTFunction {
      PTFunction( boost::packaged_task<Result> * pt) : pt(pt) {}
      boost::packaged_task<Result> * pt;
      void operator() () {
        (*pt)();
      }
    };

    template<typename Result>
    static boost::function0<void> mkPT(boost::packaged_task<Result> * pt) {
      return PTFunction<Result>(pt);
    }

    template<typename Context>
    struct SolveCaller 
    {
      SolveCaller( Context & ctx)
        : ctx(ctx) {}
      bool operator() () 
      {
        return metaSMT::solve(ctx);
      }
      Context & ctx;
    };

    template<typename Context, typename Expr >
    struct ReadCaller 
    {
      ReadCaller( Context & ctx, Expr e)
        : ctx(ctx), e(e) {}
      result_wrapper* operator() () 
      {
        return new result_wrapper(metaSMT::read_value(ctx, e));
      }
      Context & ctx;
      Expr e;
    };

    template<typename Context, typename Command, typename Param1>
    struct CommandCaller
    {
      CommandCaller( Context & ctx, Param1 param )
        : ctx(ctx), param(param) {}
      void operator() () 
      {
        ctx.command(Command(), getValue(param) );
      }

      template <typename T>
        T getValue( T const & t) {return t;} 

      template <typename T>
        T getValue( boost::shared_future<T> & t) {return t.get();} 
      Context & ctx;
      Param1 param;
    };

    template<typename Context, typename Command, typename Param1>
    CommandCaller <Context, Command, Param1>
    call_command( Context & ctx, Command const & cmd, Param1 param1) {
      return CommandCaller <Context, Command, Param1>(ctx, param1);
    }


    typedef boost::fusion::vector<
      boost::shared_future<typename SolverContext1::result_type>,
      boost::shared_future<typename SolverContext2::result_type>
      > result_type;

    template<int N>
    struct unpack_future 
    : proto::or_<
      proto::when< 
        proto::terminal< result_type >
      , proto::_make_terminal(
          //, boost::proto::terminal < 
          //	typename boost::fusion::result_of::at<result_type, boost::mpl::int_<N> >::type
          //  > ( boost::
          proto::functional::at ( proto::_value, boost::mpl::int_<N> () )
        )>
          //  , proto::terminal< proto::_ >
      , proto::nary_expr<proto::_, proto::vararg< unpack_future<N> > >
    > {};

    void command( set_option_cmd const &tag, std::string const &key, std::string const &value ) {
      opt.set(key, value);
    }

    std::string command( get_option_cmd const &, std::string const &key ) {
      return opt.get(key);
    }

    std::string command( get_option_cmd const &, std::string const &key, std::string const &default_value ) {
      return opt.get(key, default_value);
    }

    /** \endcond */

    /**
     * \brief evaluate an expression in both contexts
     *
     * Takes the current expression and creates a task for each Context.
     * The tasks are put into the respective queues and the future results 
     * are returned as result_type.
     * 
     * \param e The expression to evaluate
     * \return result_type - tuple of future results of the contexts
     *
     */
    template<typename Expr>
    result_type evaluate(Expr const & e) {

      boost::packaged_task <typename SolverContext1::result_type>* pt1
        = new boost::packaged_task<typename SolverContext1::result_type>(metaSMT::lazy(*ctx1, unpack_future<0>()(e) ));

      boost::packaged_task <typename SolverContext2::result_type>* pt2
        = new boost::packaged_task<typename SolverContext2::result_type>(metaSMT::lazy(*ctx2, unpack_future<1>()(e) ));

      worker1.push(mkPT(pt1));
      worker2.push(mkPT(pt2));

      boost::shared_future<typename SolverContext1::result_type> future1 ( pt1->get_future() );
      boost::shared_future<typename SolverContext2::result_type> future2 ( pt2->get_future() );

      result_type r(future1, future2);
      return r; 
    }

    /**
     * \brief read the backend result from an expression of the last call of solve
     *
     * This method reads the result of the last call of solve for bitvectors
     * and predicates. It takes an expression and creates a task for the 
     * respective context. Dependent on the result of the solver, the task is 
     * put into the respective queue and the result is returned as 
     * result_wrapper. 
     * 
     * \param e The expression to read 
     * \return result_wrapper 
     *
     */
    template<typename Expr>
    result_wrapper read_value (Expr const & e)
    {
      if( lastSAT == 1 )  {
        boost::packaged_task <result_wrapper*>* pt1
          = new boost::packaged_task<result_wrapper*>( 
              ReadCaller<SolverContext1, Expr>(*ctx1, e) );
        worker1.push(mkPT(pt1));

        std::auto_ptr<result_wrapper> ptr( pt1->get_future().get() );
        std::cout << "read from 1: " <<  *ptr << std::endl;
        return  *ptr;

      } else if (lastSAT == 2) {
        boost::packaged_task <result_wrapper*>* pt2
          = new boost::packaged_task<result_wrapper*>( 
              ReadCaller<SolverContext2, Expr>(*ctx2, e) );
        worker2.push(mkPT(pt2));

        std::auto_ptr<result_wrapper> ptr( pt2->get_future().get() );
        std::cout << "read from 2: " <<  *ptr << std::endl;
        return  *ptr;
      } 
      return result_wrapper("X");
    }

    /**
     * \brief read the value from a result_type of the last call of solve
     *
     * Reads the result of the call of solve only for result_types.
     * Dependent to the result of the solver, the result_type is put 
     * into a tasks and then pushed into the respective queue.
     * This method returns a result_wrapper.  
     * 
     * \param e result_type to read 
     * \return result_wrapper
     *
     */
    result_wrapper read_value (result_type & e)
    {
      using boost::fusion::at_c;
      if( lastSAT == 1 )  {
        boost::packaged_task <result_wrapper*>* pt1
          = new boost::packaged_task<result_wrapper*>( 
              ReadCaller<SolverContext1, typename SolverContext1::result_type>(*ctx1, at_c<0>(e).get()) );
        worker1.push(mkPT(pt1));

        std::auto_ptr<result_wrapper> ptr( pt1->get_future().get() );
        std::cout << "read from 1': " <<  *ptr << std::endl;
        return  *ptr;

      } else if (lastSAT == 2) {
        boost::packaged_task <result_wrapper*>* pt2
          = new boost::packaged_task<result_wrapper*>( 
              ReadCaller<SolverContext2, typename SolverContext2::result_type>(*ctx2, at_c<1>(e).get()) );
        worker2.push(mkPT(pt2));

        std::auto_ptr<result_wrapper> ptr( pt2->get_future().get() );
        std::cout << "read from 2': " <<  *ptr << std::endl;
        return  *ptr;
      } 
      return result_wrapper("X");

    }

    /**
     * \brief insert a result_type into queues
     *
     * Takes a result_type and split it into the respective queues.
     * 
     * \param cmd  - a Command
     * \param e - a result_type
     * \return void
     *
     */
    template<typename Command>
    void command( Command const & cmd, result_type e) 
    {
      worker1.push( call_command (*ctx1, cmd, boost::fusion::at_c<0>(e)) );
      worker2.push( call_command (*ctx2, cmd, boost::fusion::at_c<1>(e)) );
    }

    /**
     * \brief insert an argument into queues
     *
     * This method takes an argument and push it into the two queues.
     * 
     * \param cmd - a Command
     * \param a1 - an argument
     * \return void
     *
     */

    template<typename Command, typename Arg1>
    void command( Command const & cmd, Arg1 a1) 
    {
      worker1.push( call_command (*ctx1, cmd, a1) );
      worker2.push( call_command (*ctx2, cmd, a1) );
    }


    bool solve()
    {
      boost::packaged_task <bool>* pt1
        = new boost::packaged_task<bool>( SolveCaller<SolverContext1>(*ctx1) );
      boost::packaged_task <bool>* pt2
        = new boost::packaged_task<bool>( SolveCaller<SolverContext2>(*ctx2) );


      worker1.push(mkPT(pt1));
      worker2.push(mkPT(pt2));

      boost::unique_future<bool> future1 = pt1->get_future();
      boost::unique_future<bool> future2 = pt2->get_future();

      unsigned id = 1 + boost::wait_for_any(future1, future2);
      lastSAT = id;

      std::cout << "erster: " << id << std::endl;
      if( id == 1 ) {
        return future1.get();
      }

      return future2.get();
    }


    private:
      Options opt;
      boost::shared_ptr<SolverContext1> ctx1;
      boost::shared_ptr<SolverContext2> ctx2;

      concurrent::ThreadedWorkerWrapper<SolverContext1> worker1;
      concurrent::ThreadedWorkerWrapper<SolverContext2> worker2;

      boost::thread thread1;
      boost::thread thread2;


      // the id of the solver which returned the last SAT result in solve,
      // 0: UNSAT/invalid
      // 1: ctx1
      // 2: ctx2
      unsigned lastSAT;

      // disable copying DirectSolvers; 
      Threaded_Context(Threaded_Context const & );
      Threaded_Context& operator=(Threaded_Context const & );
  };

  namespace features {
  //  template<typename Context, typename Feature>
  //  struct supports< Threaded_Context<Context>, Feature>
  //  : supports<Context, Feature>::type {};

 template<typename Context1, typename Context2, typename Feature>
  struct supports< Threaded_Context<Context1, Context2>, Feature>
  : boost::mpl::and_<
    typename supports<Context1, Feature>::type,
    typename supports<Context2, Feature>::type
  >::type {};

    template<typename Context1, typename Context2>
    struct supports< Threaded_Context<Context1, Context2>, get_option_cmd>
    : boost::mpl::true_ {};

    template<typename Context1, typename Context2>
    struct supports< Threaded_Context<Context1, Context2>, set_option_cmd>
    : boost::mpl::true_ {};

  }

  template <typename SolverType1, typename SolverType2, typename Expr>
  typename boost::disable_if<
    typename boost::is_same<Expr, typename Threaded_Context<SolverType1, SolverType2>::result_type>::type,
    typename Threaded_Context<SolverType1, SolverType2>::result_type
  >::type
  evaluate( Threaded_Context<SolverType1, SolverType2> & ctx, Expr const & e ) {
    return ctx.evaluate(e);
  }

  template <typename SolverType1, typename SolverType2>
  typename Threaded_Context<SolverType1, SolverType2>::result_type
  evaluate( Threaded_Context<SolverType1, SolverType2> & ctx,
            typename Threaded_Context<SolverType1, SolverType2>::result_type r ) {
    return r;
  }

  template <typename SolverType1, typename SolverType2>
  bool solve( Threaded_Context<SolverType1, SolverType2> & ctx) {
    return ctx.solve();
  }

  template <typename SolverType1, typename SolverType2>
  result_wrapper 
  read_value(
      Threaded_Context<SolverType1, SolverType2> & ctx
    , logic::QF_BV::bitvector const & var) 
  {
    return ctx.read_value( var );
  }


  template <typename SolverType1, typename SolverType2>
  result_wrapper 
  read_value(
      Threaded_Context<SolverType1, SolverType2> & ctx
    , logic::predicate const & var) 
  {
    return ctx.read_value( var );
  }

  template <typename SolverType1, typename SolverType2>
  result_wrapper 
  read_value(
      Threaded_Context<SolverType1,SolverType2> & ctx
    , typename Threaded_Context<SolverType1,SolverType2>::result_type var) 
  {
    return ctx.read_value( var );
  }

} // namespace metaSMT 

//  vim: ft=cpp:ts=2:sw=2:expandtab
