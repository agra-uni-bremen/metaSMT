#pragma once

#include "support/SMT_Graph.hpp"
#include "Graph_Context.hpp"
#include "result_wrapper.hpp"
#include "Features.hpp"
#include "support/Options.hpp"
#include "API/Assertion.hpp"
#include "API/Assumption.hpp"
#include "API/Options.hpp"

#include <boost/foreach.hpp>
#include <boost/shared_ptr.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>

#include <vector>

namespace metaSMT {

  template <typename Callee, typename T>
  struct CallByTag {
    CallByTag(Callee * callee, std::vector<T> const & args, boost::any const & arg)
      : callee(callee), args(args), arg(arg) {}


    typedef typename Callee::result_type result_type;

    template <typename TagT>
    result_type operator() (TagT tag) const {
      switch(args.size()) {
        case 0:
          //printf("call op0\n");
          return (*callee)( tag, arg );
        case 1:
          //printf("call op1\n");
          return (*callee)( tag, args[0] );
        case 2:
          //printf("call op2\n");
          return (*callee)( tag, args[0], args[1] );
        case 3:
          //printf("call op3\n");
          return (*callee)( tag, args[0], args[1], args[2] );
        default:
          assert( false && "unexpeced case" );
      }
      throw std::runtime_error("unexpected");
    }

    result_type operator() (metaSMT::logic::QF_BV::tag::extract_tag tag) const {
      assert(args.size() > 0);
      assert(args.size() == 1);
      unsigned long upper, lower;
      boost::tie(upper, lower) 
        = boost::any_cast<boost::tuple<unsigned long, unsigned long> >(arg);
      return (*callee)( tag, upper, lower, args.front() );
    }

    result_type operator() (metaSMT::logic::QF_BV::tag::zero_extend_tag tag) const {
      assert(args.size() > 0);
      assert(args.size() == 1);
      unsigned long width
        = boost::any_cast< unsigned long >(arg);
      return (*callee)( tag, width, args.front() );
    }

    result_type operator() (metaSMT::logic::QF_BV::tag::sign_extend_tag tag) const {
      assert(args.size() > 0);
      assert(args.size() == 1);
      unsigned long width
        = boost::any_cast< unsigned long >(arg);
      return (*callee)( tag, width, args.front() );
    }
    
    mutable Callee       * callee;
    std::vector<T> const & args;
    boost::any     const & arg;
  };

  template <typename Callee, typename T>
  CallByTag<Callee, T> make_callByTag(Callee * callee, std::vector<T> const & args, boost::any const & arg) {
    return CallByTag<Callee, T>(callee, args, arg);
  }


  /**
   *  GraphSolver_Context takes a SolverType. All constraints are first
   *  forwarded to a Graph_Context, for deduplication and later handed to
   *  solver.
   **/
  template<typename SolverContext>
  struct GraphSolver_Context {

    GraphSolver_Context ( ) 
      : _gtx( new Graph_Context() ) {
      typedef typename boost::mpl::if_<
        /* if   = */ typename features::supports< SolverContext, setup_option_map_cmd >::type
      , /* then = */ option::SetupOptionMapCommand
      , /* else = */ option::NOPCommand
      >::type Command;
      Command::template action( _solver, _opt );
    }

    explicit GraphSolver_Context ( const GraphSolver_Context & ctx )
      : _opt( ctx._opt )
      , _gtx( ctx._gtx ) // share graph
      , _solver() // create new solver
      , _lookup() // create new lookup table
      , _assertions( ctx._assertions )   // copy assertions
      , _assumptions( ctx._assumptions ) // copy assumptions
    {
      BOOST_FOREACH(SMT_Expression e, _assertions) {
        _solver.assertion ( _eval(e) );
      }
      BOOST_FOREACH(SMT_Expression e, _assumptions) {
        _solver.assumption ( _eval(e) );
      }
    }

    typedef SolverContext solver_type;
    typedef SMT_Expression result_type;
    typedef typename SolverContext::result_type solver_result;

    void assertion ( SMT_Expression e ) {
      namespace ph=boost::phoenix;
      _assertions.push_back(e);

      Cmd f = 
        ph::bind( &SolverContext::assertion, ph::ref(_solver),
          ph::bind(&GraphSolver_Context<SolverContext>::_eval, ph::ref(*this), e )
        );
      _cmd_queue.push_back(f);
    }

    void assumption( SMT_Expression e ) {
      _assumptions.push_back(e);
    }

    template< typename Context, typename CMD, typename Arg1 >
    struct Cmd_Caller1 {
      Cmd_Caller1( Context & ctx, CMD c, Arg1 a1)
      : ctx(ctx), cmd(c), arg1(a1) { }

      void operator() (){ ctx.command(cmd, arg1); }

      Context & ctx;
      CMD cmd;
      Arg1 arg1;
    };

    template< typename Context, typename CMD >
    struct Cmd_Caller0 {
      Cmd_Caller0( Context & ctx, CMD c)
      : ctx(ctx), cmd(c) { }

      void operator() (){ ctx.command(cmd); }

      Context & ctx;
      CMD cmd;
    };

    template <typename CMD, typename Arg>
    typename boost::enable_if< boost::is_same< typename CMD::result_type, void> >::type
    command (CMD const & cmd, Arg arg) 
    {
      Cmd f = 
        Cmd_Caller1<SolverContext, CMD, Arg>(_solver, cmd, arg);
      _cmd_queue.push_back(f);
    }

    template <typename CMD>
    typename boost::enable_if< boost::is_same< typename CMD::result_type, void> >::type
    command (CMD const & cmd) 
    {
      Cmd f = 
        Cmd_Caller0<SolverContext, CMD>(_solver, cmd);
      _cmd_queue.push_back(f);
    }

    template <typename CMD>
    typename CMD::result_type command(CMD const & cmd)
    {
      sync();
      return _solver.command(cmd);
    }

    void command( assertion_cmd const &, result_type e) {
      assertion(e);
    }
    void command( assumption_cmd const &, result_type e) {
      assumption(e);
    }

    void command( set_option_cmd const &tag, std::string const &key, std::string const &value ) {
      _opt.set(key, value);
      typedef typename boost::mpl::if_<
        /* if   = */ typename features::supports< SolverContext, set_option_cmd >::type
      , /* then = */ option::SetOptionCommand
      , /* else = */ option::NOPCommand
      >::type Command;
      Command::template action( _solver, _opt );
    }

    std::string command( get_option_cmd const &, std::string const &key ) {
      return _opt.get(key);
    }

    std::string command( get_option_cmd const &, std::string const &key, std::string const &default_value ) {
      return _opt.get(key, default_value);
    }

    void sync() {
      BOOST_FOREACH( Cmd const & f, _cmd_queue) {
        f();
      }
      _cmd_queue.clear();
    }

    bool solve() {
      sync();
      //BOOST_FOREACH(SMT_Expression e, _assertions) {
      //  _solver.assertion ( _eval(e) );
      //}
      BOOST_FOREACH(SMT_Expression e, _assumptions) {
        _solver.assumption ( _eval(e) );
      }
      _assumptions.clear();
      return _solver.solve();
    }

    void write_smt(std::ostream &os) {
      SMT_ExprContainer v;
      std::copy(_assertions.begin(), _assertions.end(),
                std::back_inserter(v));
      std::copy(_assumptions.begin(), _assumptions.end(),
                std::back_inserter(v));
      _gtx->write_smt(os, v);
    }

    void write_smt(std::ostream &os, result_type r) {
      SMT_ExprContainer v(1,r);
      _gtx->write_smt(os, v);
    }

    struct create_x_result : boost::static_visitor<result_wrapper> 
    {
      template<typename T>
      result_type operator() (T) const {
        return result_wrapper(&boost::logic::indeterminate);
      }
      
      result_type operator() (logic::QF_BV::tag::var_tag const & var) const {
        std::vector<boost::logic::tribool> ret ( var.width
            ,  boost::logic::indeterminate);
        return result_wrapper(ret);
      }
    };

    result_wrapper read_value(SMT_Expression var)
    { 
      typename LookupT::const_iterator ite
        = _lookup.find(var);
      if ( ite != _lookup.end() ) {
        return _solver.read_value( _eval( var ) ); 
      } else {
        return boost::apply_visitor(create_x_result()
            , boost::get(boost::vertex_tag, _gtx->graph(), var));
      }
    }

    template <typename Expr>
    SMT_Expression evaluate ( Expr e ) { return ::metaSMT::evaluate(*_gtx, e); }

    SMT_Expression evaluate ( result_type r ) { return r; }

    private:
      solver_result  _eval( SMT_Expression e) {
        typename LookupT::const_iterator ite = _lookup.find(e);
        if ( ite != _lookup.end() ) {
          return ite->second;
        }

        SMT_Graph const & g = _gtx->graph();

        std::vector<solver_result> args;
        // ... fill args
        BOOST_FOREACH(SMT_Edge k, out_edges(e,g)) {
          args.push_back( _eval(target(k,g)) );
        }
        
        boost::any arg = boost::get(boost::vertex_arg, g, e);
        Tag tag        = boost::get(boost::vertex_tag, g, e);

        solver_result ret = boost::apply_visitor( make_callByTag(&_solver, args, arg), tag); 
        _lookup.insert( std::make_pair(e, ret) );
        return ret;
      };

      Options _opt;
      boost::shared_ptr<Graph_Context> _gtx;
      solver_type _solver;
      typedef typename std::map<SMT_Expression, solver_result> LookupT;
      typedef boost::function0<void> Cmd;
      typedef std::list< Cmd > Cmd_Queue;
      typedef std::vector<SMT_Expression> SMT_ExprContainer;
      LookupT _lookup;
      SMT_ExprContainer _assertions;
      SMT_ExprContainer _assumptions;
      Cmd_Queue _cmd_queue;
  };

  namespace features {
    template<typename Context, typename Feature>
    struct supports< GraphSolver_Context<Context>, Feature>
    : supports<Context, Feature>::type {};

    template<typename Context>
    struct supports< GraphSolver_Context<Context>, assertion_cmd>
    : boost::mpl::true_ {};

    template<typename Context>
    struct supports< GraphSolver_Context<Context>, assumption_cmd>
    : boost::mpl::true_ {};

    template<typename Context>
    struct supports< GraphSolver_Context<Context>, set_option_cmd>
    : boost::mpl::true_ {};

    template<typename Context>
    struct supports< GraphSolver_Context<Context>, get_option_cmd>
    : boost::mpl::true_ {};
  }

  template <typename SolverTypes, typename Expr>
  SMT_Expression evaluate( GraphSolver_Context<SolverTypes> & ctx, Expr const & e ) {
    return  ctx.evaluate(e) ;
  }

  template <typename SolverTypes>
  bool solve( GraphSolver_Context<SolverTypes> & ctx) {
    return ctx.solve();
  }

  template <typename SolverTypes>
  void write_smt( GraphSolver_Context<SolverTypes> & ctx, std::ostream &os ) {
    ctx.write_smt(os);
  }

  template <typename SolverTypes>
  result_wrapper 
  read_value(
      GraphSolver_Context<SolverTypes> & ctx
    , logic::QF_BV::bitvector const & var) 
  {
    return ctx.read_value( evaluate(ctx, var) );
  }

  template <typename SolverTypes>
  result_wrapper 
  read_value(
      GraphSolver_Context<SolverTypes> & ctx
    , logic::predicate const & var) 
  {
    return ctx.read_value( evaluate(ctx, var) );
  }

  template <typename SolverTypes>
  result_wrapper 
  read_value(
      GraphSolver_Context<SolverTypes> & ctx
    , SMT_Expression const & var) 
  {
    return ctx.read_value( var );
  }

} // namespace metaSMT 

//  vim: ft=cpp:ts=2:sw=2:expandtab
