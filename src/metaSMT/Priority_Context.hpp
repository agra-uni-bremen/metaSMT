#pragma once

#include "result_wrapper.hpp"
#include "frontend/Logic.hpp"
#include "frontend/QF_BV.hpp"
#include "Features.hpp"
#include "support/lazy.hpp"
#include "support/protofy.hpp"
#include "API/BoolEvaluator.hpp"
#include "API/Options.hpp"
#include "concurrent/Threaded_Worker.hpp"

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
#include <boost/fusion/sequence/io.hpp>
#include <boost/fusion/sequence/intrinsic/at.hpp>

#include <vector>
#include <iostream>
#include <pthread.h>

namespace metaSMT {

  /**
   * @brief Multi-multiple solver contexts and dispatches all calls
   * (assertions/assumptions) to both of them in parallel. After the "prioritized" solver context is ready then it is used exclusively.
   *
   * \tparam SolverContext1 a valid metaSMT context, e.g. DirectSolver_Context<...>
   * \tparam SolverContext2 another valid metaSMT context
   **/
  template<typename SolverContext1, typename SolverContext2>
  struct Priority_Context
  : boost::proto::callable_context< Priority_Context<SolverContext1, SolverContext2>, boost::proto::null_context >
  {
    Priority_Context()
      : ctx1(new SolverContext1)
      , ctx2(new SolverContext2)
      , worker1(ctx1)
      , worker2(ctx2)
      , thread1(worker1)
      , thread2(worker2)
      , lastSAT(0)
      , ready(new bool(false))
      , counter0(0)
      , counter1(0)
    {}

    /**
     * \brief controls the running threads
     *
     * The destructor regulates the threads by interrupting and joining
     * the threads.
     *
     */
    ~Priority_Context() {
      thread1.interrupt();
      thread2.interrupt();
      //pthread_cancel(thread1.native_handle());
      //pthread_cancel(thread2.native_handle());
      //thread1.join();
      //thread2.join();

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
          proto::functional::at ( proto::_value, boost::mpl::int_<N> () )
          )>
      , proto::nary_expr<proto::_, proto::vararg< unpack_future<N> > >
    > {};

    template<typename Command>
    void command( Command const & cmd, result_type e)
    {
      worker1.push( call_command (*ctx1, cmd, boost::fusion::at_c<0>(e)) );
      worker2.push( call_command (*ctx2, cmd, boost::fusion::at_c<1>(e)) );
    }


    template<typename Command, typename Arg1>
    void command( Command const & cmd, Arg1 a1)
    {
      worker1.push( call_command (*ctx1, cmd, a1) );
      worker2.push( call_command (*ctx2, cmd, a1) );
    }

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
     * Tasks are put into the respective queues and read by future tag.
     * The future results are returned as result_type.
     *
     * \param e The expression to evaluate
     * \return result_type - tuple of future results of the contexts
     *
     */
    template<typename Expr>
    result_type evaluate(Expr const & e)
    {
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
     * \brief read the value of an expression in both contexts
     *
     * after a retrieval of the solver, the current expression is taken and created a task for each Context.
     * Both tasks are put into the respective queues and read by future tags.
     * The results of the futures are returned as result_wrapper.
     *
     * \param e The expression to read
     * \return result_wrapper - tuple of results of the contexts
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
        //std::cout << "read from 1: " <<  *ptr << std::endl;
        return  *ptr;

      } else if (lastSAT == 2) {
        boost::packaged_task <result_wrapper*>* pt2
          = new boost::packaged_task<result_wrapper*>(
              ReadCaller<SolverContext2, Expr>(*ctx2, e) );
        worker2.push(mkPT(pt2));

        std::auto_ptr<result_wrapper> ptr( pt2->get_future().get() );
        //std::cout << "read from 2: " <<  *ptr << std::endl;
        return  *ptr;
      }
      return result_wrapper("X");
    }

    /**
     * \brief read the value of a result_type in both contexts
     *
     * Takes the current expression and creates a task for each Context, after a retrieval of the solver.
     * Tasks are put into the respective queues and read by the future tag.
     * The future results are returned as result_wrapper.
     *
     * \param e The result-type to read
     * \return result_wrapper - tuple of results of the contexts
     *
     */
    result_wrapper read_value (result_type & e)
    {
      namespace fu =  boost::fusion;
      if( lastSAT == 1 )  {
        boost::packaged_task <result_wrapper*>* pt1
          = new boost::packaged_task<result_wrapper*>(
              ReadCaller<SolverContext1, typename SolverContext1::result_type>(*ctx1, fu::at_c<0>(e).get()) );
        worker1.push(mkPT(pt1));

        std::auto_ptr<result_wrapper> ptr( pt1->get_future().get() );
        //std::cout << "read from 1': " <<  *ptr << std::endl;
        return  *ptr;

      } else if (lastSAT == 2) {
        boost::packaged_task <result_wrapper*>* pt2
          = new boost::packaged_task<result_wrapper*>(
              ReadCaller<SolverContext2, typename SolverContext2::result_type>(*ctx2, fu::at_c<1>(e).get()) );
        worker2.push(mkPT(pt2));

        std::auto_ptr<result_wrapper> ptr( pt2->get_future().get() );
        //std::cout << "read from 2': " <<  *ptr << std::endl;
        return  *ptr;
      }
      return result_wrapper("X");

    }

    /**
     * \brief controls the order of the solver
     *
     * Puts the contexts into each queues and retrieves, which solver was last called.
     * The future results are returned as bool.
     *
     * \return bool - task with respective value
     *
     */
    bool solve()
    {
      //std::cout << "solve called" << std::endl;
      boost::packaged_task <bool>* pt1
        = new boost::packaged_task<bool>( SolveCaller<SolverContext1>(*ctx1) );

      boost::unique_future<bool> future1 = pt1->get_future();
      worker1.push(mkPT(pt1));

      if(*ready)
      {
        counter0++;
        lastSAT = 1;
        return future1.get();
      }

      boost::packaged_task <bool>* pt2
        = new boost::packaged_task<bool>( SolveCaller<SolverContext2>(*ctx2) );
      boost::function0<void> newFunc
        = boost::bind(&Priority_Context::setReady, ready );

      worker1.push(newFunc);

      worker2.push(mkPT(pt2));

      boost::unique_future<bool> future2 = pt2->get_future();

      unsigned id = 1 + boost::wait_for_any(future1, future2);
      lastSAT = id;

      //std::cout << "erster: " << id << std::endl;
      if( id == 1 ) {
        counter0++;
        return future1.get();
      }
      counter1++;
      return future2.get();
    }

    /**
     * \brief  get the value of a variable
     *
     * Gives back the value of the current variable.
     * \return unsigend - the value of the variable
     *
     */
    unsigned get_count0()
    {
      return counter0;
    }

    /**
     * \brief  get the value of a variable
     *
     * Gives back the value of the current variable.
     * \return unsigend - the value of the variable
     *
     */
    unsigned get_count1()
    {
      return counter1;
    }

    /**
     * \brief  set the value of a bool variable
     *
     * Takes a variable and set his value true.
     *
     * \param ready - current variable
     * \return void
     *
     */
    static void setReady( boost::shared_ptr<bool> ready )
    {
      //std::cout << "now ready" << std::endl;
      *ready = true;
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
    boost::shared_ptr<bool> ready;
    unsigned counter0;
    unsigned counter1;

    // disable copying DirectSolvers;
    Priority_Context(Priority_Context const & );
    Priority_Context& operator=(Priority_Context const & );
  };

  namespace features {
    //  template<typename Context, typename Feature>
    //  struct supports< Threaded_Context<Context>, Feature>
    //  : supports<Context, Feature>::type {};

    template<typename Context1, typename Context2, typename Feature>
    struct supports< Priority_Context<Context1, Context2>, Feature>
    : boost::mpl::and_<
      typename supports<Context1, Feature>::type,
      typename supports<Context2, Feature>::type
    >::type {};

    template<typename Context1, typename Context2>
    struct supports< Priority_Context<Context1, Context2>, get_option_cmd>
    : boost::mpl::true_ {};

    template<typename Context1, typename Context2>
    struct supports< Priority_Context<Context1, Context2>, set_option_cmd>
    : boost::mpl::true_ {};
  } // features

  template <typename SolverType1, typename SolverType2>
  typename Priority_Context<SolverType1, SolverType2>::result_type
  evaluate( Priority_Context<SolverType1, SolverType2> & ctx,
        typename Priority_Context<SolverType1, SolverType2>::result_type r
  ) {
    return r;
  }

  template <typename SolverType1, typename SolverType2, typename Expr>
    typename boost::disable_if<
      typename boost::mpl::or_<
        typename boost::is_same<Expr, typename Priority_Context<SolverType1, SolverType2>::result_type>::type
      , typename Evaluator<Expr>::type
      >::type
    , typename Priority_Context<SolverType1, SolverType2>::result_type
  >::type
  evaluate( Priority_Context<SolverType1, SolverType2> & ctx, Expr const & e ) {
    return ctx.evaluate(e);
  }

  template < typename SolverType1, typename SolverType2, typename Expr >
  typename boost::enable_if<
    typename Evaluator<Expr>::type
  , typename Priority_Context<SolverType1, SolverType2>::result_type
  >::type
  evaluate( Priority_Context<SolverType1, SolverType2> &ctx, Expr const &e ) {
    return Evaluator<Expr>::eval(ctx, e);
  }

  template <typename SolverType1, typename SolverType2>
  bool solve( Priority_Context<SolverType1, SolverType2> & ctx) {
    return ctx.solve();
  }


  template <typename SolverType1, typename SolverType2>
  result_wrapper
  read_value(
      Priority_Context<SolverType1, SolverType2> & ctx
      , logic::QF_BV::bitvector const & var)
  {
    return ctx.read_value( var );
  }


  template <typename SolverType1, typename SolverType2>
  result_wrapper
  read_value(
      Priority_Context<SolverType1, SolverType2> & ctx
      , logic::predicate const & var)
  {
    return ctx.read_value( var );
  }

  template <typename SolverType1, typename SolverType2>
  result_wrapper
  read_value(
    Priority_Context<SolverType1,SolverType2> & ctx
    , typename Priority_Context<SolverType1,SolverType2>::result_type var)
  {
    return ctx.read_value( var );
  }

} // namespace metaSMT

