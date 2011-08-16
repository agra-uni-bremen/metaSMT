#pragma once

#include "result_wrapper.hpp"
#include "frontend/Logic.hpp"
#include "frontend/QF_BV.hpp"
#include "Features.hpp"
#include "API/Assertion.hpp"
#include "API/Assumption.hpp"
#include "support/concurrent_queue.hpp"
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

  template<typename SolverContext1, typename SolverContext2>
  struct Priority_Context 
    : boost::proto::callable_context< Priority_Context<SolverContext1, SolverContext2>, boost::proto::null_context >
  { 
   Priority_Context()
   	: ready(false)
	  ,counter0(0)
	  ,counter1(0)
	  ,t_1(worker, 1, boost::ref(queue1))
          ,t_2(worker, 2, boost::ref(queue2))    {}

    ~Priority_Context() {
      t_1.interrupt();
      t_2.interrupt();
      t_1.join();
      t_2.join();
    }

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
  
  template<typename Expr>
   result_type evaluate(Expr const & e) 
    {
      boost::packaged_task <typename SolverContext1::result_type>* pt1
	  = new boost::packaged_task<typename SolverContext1::result_type>(lazy(ctx1, unpack_future<0>()(e) ));
    
      boost::packaged_task <typename SolverContext2::result_type>* pt2
	  = new boost::packaged_task<typename SolverContext2::result_type>(lazy(ctx2, unpack_future<1>()(e) ));
 
	
      queue1.push(mkPT(pt1));
      queue2.push(mkPT(pt2));
 
      boost::shared_future<typename SolverContext1::result_type> future1 ( pt1->get_future() );
      boost::shared_future<typename SolverContext2::result_type> future2 ( pt2->get_future() );

      result_type r(future1, future2);
      return r; 
    }

 template<typename Expr>
    result_wrapper read_value (Expr const & e)
    {
    	if( lastSAT == 1 )  {
	  boost::packaged_task <result_wrapper*>* pt1
	     = new boost::packaged_task<result_wrapper*>( 
	     	ReadCaller<SolverContext1, Expr>(ctx1, e) );
 	  queue1.push(mkPT(pt1));

	  std::auto_ptr<result_wrapper> ptr( pt1->get_future().get() );
	  std::cout << "read from 1: " <<  *ptr << std::endl;
	  return  *ptr;

	} else if (lastSAT == 2) {
	  boost::packaged_task <result_wrapper*>* pt2
	     = new boost::packaged_task<result_wrapper*>( 
	     	ReadCaller<SolverContext2, Expr>(ctx2, e) );
 	  queue2.push(mkPT(pt2));

	  std::auto_ptr<result_wrapper> ptr( pt2->get_future().get() );
	  std::cout << "read from 2: " <<  *ptr << std::endl;
	  return  *ptr;
	} 
	return result_wrapper("X");
    }
  result_wrapper read_value (result_type & e)
    {
    	using boost::fusion::at_c;
    	if( lastSAT == 1 )  {
	  boost::packaged_task <result_wrapper*>* pt1
	     = new boost::packaged_task<result_wrapper*>( 
	     	ReadCaller<SolverContext1, typename SolverContext1::result_type>(ctx1, at_c<0>(e).get()) );
 	  queue1.push(mkPT(pt1));

	  std::auto_ptr<result_wrapper> ptr( pt1->get_future().get() );
	  std::cout << "read from 1': " <<  *ptr << std::endl;
	  return  *ptr;
		
	} else if (lastSAT == 2) {
	  boost::packaged_task <result_wrapper*>* pt2
	     = new boost::packaged_task<result_wrapper*>( 
	     	ReadCaller<SolverContext2, typename SolverContext2::result_type>(ctx2, at_c<1>(e).get()) );
 	  queue2.push(mkPT(pt2));

	  std::auto_ptr<result_wrapper> ptr( pt2->get_future().get() );
	  std::cout << "read from 2': " <<  *ptr << std::endl;
	  return  *ptr;
	} 
	  return result_wrapper("X");
	
    }

    static void worker ( int id, concurrent_queue<boost::function0<void> > & queue) {
	 while(true) { 
	  boost::function0<void> task = NULL;
	  queue.wait_and_pop(task);
          task();
 	 }
    }

    template<typename Command>
    void command( Command const & cmd, result_type e) 
     {
      queue1.push( call_command (ctx1, cmd, boost::fusion::at_c<0>(e)) );
      queue2.push( call_command (ctx2, cmd, boost::fusion::at_c<1>(e)) );
     }


    template<typename Command, typename Arg1>
    void command( Command const & cmd, Arg1 a1) 
     {
      queue1.push( call_command (ctx1, cmd, a1) );
      queue2.push( call_command (ctx2, cmd, a1) );
     }


   bool solve()
    {

      boost::packaged_task <bool>* pt1
	  = new boost::packaged_task<bool>( SolveCaller<SolverContext1>(ctx1) );
	   
      boost::unique_future<bool> future1 = pt1->get_future();
      queue1.push(mkPT(pt1));

      if(ready)
      {
	counter0++;
	return future1.get();
      }

      boost::packaged_task <bool>* pt2
          = new boost::packaged_task<bool>( SolveCaller<SolverContext2>(ctx2) );
      boost::function0<void> newFunc 
          = boost::bind(&Priority_Context::setReady, boost::ref(ready) );	

      queue1.push(newFunc);

      queue2.push(mkPT(pt2));

      boost::unique_future<bool> future2 = pt2->get_future();

      unsigned id = 1 + boost::wait_for_any(future1, future2);
      lastSAT = id;

      std::cout << "erster: " << id << std::endl;
      if( id == 1 ) {
	 counter0++;
	 return future1.get();
      }
      counter1++;  
      return future2.get();
   } 
    
    void set_counter0( unsigned counter0)
    {
	this.counter0 = counter0;
    }

    void set_counter1( unsigned counter1)
    {
	this.counter1 = counter1;
    }
   
    unsigned get_count0()
    {
	return counter0;
    }

    unsigned get_count1()
    {
	return counter1;
    }
     static void setReady( bool &ready )
    {
      ready = true;
    }

    
    private:
    //  concurrent_queue<boost::packaged_task<bool>*> queue1;
     // concurrent_queue<boost::packaged_task<bool>*> queue2;
      
      concurrent_queue<boost::function0<void> > queue1;
      concurrent_queue<boost::function0<void> > queue2;

   
      boost::thread t_1;
      boost::thread t_2;
      boost::condition_variable cvar;

      SolverContext1 ctx1;
      SolverContext2 ctx2;

      // the id of the solver which returned the last SAT result in solve,
      // 0: UNSAT/invalid
      // 1: ctx1
      // 2: ctx2
      unsigned lastSAT;
      bool ready;
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

  }

  template <typename SolverType1, typename SolverType2, typename Expr>
  typename boost::disable_if<
    typename boost::is_same<Expr, typename Priority_Context<SolverType1, SolverType2>::result_type>::type,
    typename Priority_Context<SolverType1, SolverType2>::result_type
  >::type
  evaluate( Priority_Context<SolverType1, SolverType2> & ctx, Expr const & e ) {
    return ctx.evaluate(e);
  }

  template <typename SolverType1, typename SolverType2>
  typename Priority_Context<SolverType1, SolverType2>::result_type
  evaluate( Priority_Context<SolverType1, SolverType2> & ctx,
            typename Priority_Context<SolverType1, SolverType2>::result_type r ) {
    return r;
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

