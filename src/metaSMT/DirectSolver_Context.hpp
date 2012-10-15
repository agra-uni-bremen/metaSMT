#pragma once

#include "result_wrapper.hpp"
#include "frontend/Logic.hpp"
#include "frontend/QF_UF.hpp"
#include "frontend/QF_BV.hpp"
#include "frontend/Array.hpp"
#include "Features.hpp"
#include "API/Assertion.hpp"
#include "API/Assumption.hpp"
#include "API/Options.hpp"
#include "API/BoolEvaluator.hpp"
#include "support/Options.hpp"

#include <boost/any.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/proto/core.hpp>
#include <boost/proto/context.hpp>
#include <boost/tr1/unordered_map.hpp>

namespace metaSMT {
  /**
   * @brief direct Solver integration
   *
   *  DirectSolver_Context takes a SolverType and directly feeds all commands
   *  to it. Variable expressions are cached and only evaluated once.
   **/
  template<typename SolverContext>
  struct DirectSolver_Context 
    : SolverContext
    , boost::proto::callable_context< DirectSolver_Context<SolverContext>, boost::proto::null_context >
  { 
    DirectSolver_Context() {
      typedef typename boost::mpl::if_<
        /* if   = */ typename features::supports< SolverContext, setup_option_map_cmd >::type
      , /* then = */ option::SetupOptionMapCommand
      , /* else = */ option::NOPCommand
      >::type Command;
      Command::template action( static_cast<SolverContext&>(*this), opt );
    }

    DirectSolver_Context(Options const &opt)
      : opt(opt)
    {}

    /// The returned expression type is the result_type of the SolverContext
    typedef typename SolverContext::result_type result_type;

    // special handling of bvuint_tag
    template< typename Expr1, typename Expr2>
    result_type operator() (logic::QF_BV::tag::bvuint_tag const & tag
        , Expr1 value
        , Expr2 bw
    ) {
      const unsigned long val   = proto::value(value);
      const unsigned long width = proto::value(bw);

      return SolverContext::operator() ( tag,
        boost::any(boost::make_tuple(val, width))
      );
    }

    // special handling of bvsint_tag
    template< typename Expr1, typename Expr2>
    result_type operator() (logic::QF_BV::tag::bvsint_tag const & tag
        , Expr1 value
        , Expr2 bw
    ) {
      const long val            = proto::value(value);
      const unsigned long width = proto::value(bw);

      return  SolverContext::operator() ( tag, 
        boost::any(boost::make_tuple(val, width))
      );
    }

    // special handling of bvbin_tag
    template< typename Expr1>
    result_type operator() (logic::QF_BV::tag::bvbin_tag tag
        , Expr1 value
    ) 
    {
      const std::string val = proto::value(value);
      return  SolverContext::operator() ( tag, boost::any(val));
    }

    // special handling of bvhex_tag
    template< typename Expr1>
    result_type operator() (logic::QF_BV::tag::bvhex_tag tag
        , Expr1 value
    ) 
    {
      const std::string val = proto::value(value);
      return  SolverContext::operator() ( tag, boost::any(val));
    }

    /// handling of logic::predicate (boolean variables)
    result_type operator() (boost::proto::tag::terminal,  
        ::metaSMT::logic::tag::var_tag tag)
    {
      assert(tag.id != 0);
      typename VariableLookupT::const_iterator iter
        = _variables.find(tag.id);
      if ( iter != _variables.end() ) {
        return iter->second;
      } else {
        result_type ret = SolverContext::operator() ( tag, boost::any() );
        _variables.insert( std::make_pair(tag.id, ret) );
        return ret;
      }
    }

    /**
     * @brief result retrieval for logic::predicate (boolean variables)
     *
     * @pre solve() must be true before calling and no assertions/assumptions 
     *      may be added in between.
     *
     * @returns a result_wrapper that is converatble to boolean (and other
     *      types) containing the assignment for var, or "X" if var is not
     *      known to the solver.
     **/
    result_wrapper read_value(logic::predicate var)
    { 
      logic::tag::var_tag tag = boost::proto::value(var);
      assert(tag.id != 0);
      typename VariableLookupT::const_iterator iter
        = _variables.find(tag.id);
      if ( iter != _variables.end() ) {
        return SolverContext::read_value( boost::proto::eval(var, *this) );
      } else {
        // unknown variable
        return result_wrapper(&boost::logic::indeterminate);
      }
    }

    /**
     * @brief result retrieval for logic::QF_BV::bitvector variables
     *
     * @pre solve() must be true before calling and no assertions/assumptions 
     *      may be added in between.
     *
     * @returns a result_wrapper containing the assignment for var, or "X" if
     *      var is not known to the solver.
     **/
    result_wrapper read_value(logic::QF_BV::bitvector var)
    { 
      logic::QF_BV::tag::var_tag tag = boost::proto::value(var);
      assert(tag.id != 0);
      typename VariableLookupT::const_iterator iter
        = _variables.find(tag.id);
      if ( iter != _variables.end() ) {
        return SolverContext::read_value( boost::proto::eval(var, *this) );
      } else {
        // unknown variable
        std::vector<boost::logic::tribool> ret ( tag.width
            ,  boost::logic::indeterminate);
        return result_wrapper(ret);
      }
    }

    using SolverContext::read_value;

    result_type operator() (boost::proto::tag::terminal,  
        ::metaSMT::logic::QF_UF::tag::function_var_tag tag)
    {
      assert(tag.id != 0);
      typename VariableLookupT::const_iterator iter
        = _variables.find(tag.id);
      if ( iter != _variables.end() ) {
        return iter->second;
      } else {
        result_type ret = SolverContext::operator() ( tag, boost::any() );
        _variables.insert( std::make_pair(tag.id, ret) );
        return ret;
      }
    }

    result_type operator() (boost::proto::tag::terminal,  
        ::metaSMT::logic::Array::tag::array_var_tag tag)
    {
      assert(tag.id != 0);
      typename VariableLookupT::const_iterator iter
        = _variables.find(tag.id);
      if ( iter != _variables.end() ) {
        return iter->second;
      } else {
        result_type ret = SolverContext::operator() ( tag, boost::any() );
        _variables.insert( std::make_pair(tag.id, ret) );
        return ret;
      }
    }

    result_type operator() (boost::proto::tag::terminal,  
        ::metaSMT::logic::QF_BV::tag::var_tag tag)
    {
      assert(tag.id != 0);
      typename VariableLookupT::const_iterator iter
        = _variables.find(tag.id);
      if ( iter != _variables.end() ) {
        return iter->second;
      } else {
        result_type ret = SolverContext::operator() ( tag, boost::any() );
        _variables.insert( std::make_pair(tag.id, ret) );
        return ret;
      }
    }

    template<typename Upper, typename Lower, typename Expr>
    result_type operator() (logic::QF_BV::tag::extract_tag t
        , Upper upper
        , Lower lower
        , Expr e
    ) {
      return SolverContext::operator() ( t,
          proto::value(upper), proto::value(lower)
        , boost::proto::eval(e, *this)
      );
    }

    template<typename Width, typename Expr >
    result_type operator() (logic::QF_BV::tag::zero_extend_tag t
        , Width width
        , Expr e
    ) {
      return SolverContext::operator() ( t,
          proto::value(width)
        , boost::proto::eval(e, *this)
      );
    }

    template<typename Width, typename Expr >
    result_type operator() (logic::QF_BV::tag::sign_extend_tag t
        , Width width
        , Expr e
    ) {
      return SolverContext::operator() ( t,
          proto::value(width)
        , boost::proto::eval(e, *this)
      );
    }


    template< typename Tag>
    result_type operator() (Tag t) {
      return SolverContext::operator() ( t, boost::any() );
    }

    template< typename Tag, typename Expr1>
    result_type
    operator() (Tag t, Expr1 e1) {
      return SolverContext::operator() ( t,
          boost::proto::eval(e1, *this)
      );
    }

    template< typename Tag, typename Expr1, typename Expr2>
    result_type operator() (Tag t, Expr1 e1, Expr2 e2) {
      return SolverContext::operator() ( t,
          boost::proto::eval(e1, *this),
          boost::proto::eval(e2, *this)
      );
    }

    template< typename Tag, typename Expr1, typename Expr2, typename Expr3>
    result_type operator() (Tag t, Expr1 e1, Expr2 e2, Expr3 e3) {
      return SolverContext::operator() ( t,
          boost::proto::eval(e1, *this)
        , boost::proto::eval(e2, *this)
        , boost::proto::eval(e3, *this)
      );
    }

    template< typename Tag, typename Expr1, typename Expr2, typename Expr3, typename Expr4>
    result_type operator() (Tag t, Expr1 e1, Expr2 e2, Expr3 e3, Expr4 e4) {
      return SolverContext::operator() ( t,
          boost::proto::eval(e1, *this)
        , boost::proto::eval(e2, *this)
        , boost::proto::eval(e3, *this)
        , boost::proto::eval(e4, *this)
      );
    }


    result_type operator() (boost::proto::tag::terminal, result_type r) {
      return r;
    }

    template < typename Tag >
    typename boost::enable_if< Evaluator<Tag>, result_type >::type
    operator() ( boost::proto::tag::terminal const &, Tag const &t ) {
      return Evaluator<Tag>::eval(*this, t);
    }

    template < typename Tag >
    typename boost::disable_if< Evaluator<Tag>, result_type >::type
    operator() ( boost::proto::tag::terminal const &, Tag const &t ) {
      return SolverContext::operator()( t, boost::any() );
    }

    void command( assertion_cmd const &, result_type e) {
      SolverContext::assertion(e);
    }

    void command( assumption_cmd const &, result_type e) {
      SolverContext::assumption(e);
    }

    void command( set_option_cmd const &tag, std::string const &key, std::string const &value ) {
      opt.set(key, value);
      typedef typename boost::mpl::if_<
        /* if   = */ typename features::supports< SolverContext, set_option_cmd >::type
      , /* then = */ option::SetOptionCommand
      , /* else = */ option::NOPCommand
      >::type Command;
      Command::template action( static_cast<SolverContext&>(*this), opt, key, value );
    }

    std::string command( get_option_cmd const &, std::string const &key ) {
      return opt.get(key);
    }

    std::string command( get_option_cmd const &, std::string const &key, std::string const &default_value ) {
      return opt.get(key, default_value);
    }

    using SolverContext::command;

    private:
      typedef typename std::tr1::unordered_map<unsigned, result_type> VariableLookupT;
      VariableLookupT _variables;
      Options opt;

      // disable copying DirectSolvers;
      DirectSolver_Context(DirectSolver_Context const & );
      DirectSolver_Context& operator=(DirectSolver_Context const & );
  };

  namespace features {
    template<typename Context, typename Feature>
    struct supports< DirectSolver_Context<Context>, Feature>
    : supports<Context, Feature>::type {};

    template<typename Context>
    struct supports< DirectSolver_Context<Context>, assertion_cmd>
    : boost::mpl::true_ {};

    template<typename Context>
    struct supports< DirectSolver_Context<Context>, assumption_cmd>
    : boost::mpl::true_ {};

    template<typename Context>
    struct supports< DirectSolver_Context<Context>, get_option_cmd>
    : boost::mpl::true_ {};

    template<typename Context>
    struct supports< DirectSolver_Context<Context>, set_option_cmd>
    : boost::mpl::true_ {};
  }

  template < typename SolverType >
  typename DirectSolver_Context<SolverType>::result_type
  evaluate( DirectSolver_Context<SolverType> &ctx,
            typename DirectSolver_Context<SolverType>::result_type r ) {
    return r;
  }

  template < typename SolverType, typename Expr >
  typename boost::disable_if<
    typename boost::mpl::or_<
      typename Evaluator<Expr>::type
    , typename boost::is_same<
        Expr
      , typename DirectSolver_Context<SolverType>::result_type
      >::type
    >::type
  , typename DirectSolver_Context<SolverType>::result_type
  >::type
  evaluate( DirectSolver_Context<SolverType> &ctx, Expr const &e ) {
    return boost::proto::eval(e, ctx);
  }

  template < typename SolverType, typename Expr >
  typename boost::enable_if<
    typename Evaluator<Expr>::type
  , typename DirectSolver_Context<SolverType>::result_type
  >::type
  evaluate( DirectSolver_Context<SolverType> &ctx, Expr const &e ) {
    return Evaluator<Expr>::eval(ctx, e);
  }

  template <typename SolverType>
  bool solve( DirectSolver_Context<SolverType> & ctx) {
    return ctx.solve();
  }

  template < typename SolverType, typename Expr >
  typename boost::enable_if< Evaluator<Expr>, result_wrapper>::type
  read_value( DirectSolver_Context<SolverType> &ctx, Expr const &expr ) {
    return ctx.read_value( Evaluator<Expr>::eval(ctx, expr) );
  }
   
  template <typename SolverType>
  result_wrapper 
  read_value(
      DirectSolver_Context<SolverType> & ctx
    , logic::QF_BV::bitvector const & var) 
  {
    return ctx.read_value( var );
  }

  template <typename SolverType>
  result_wrapper 
  read_value(
      DirectSolver_Context<SolverType> & ctx
    , logic::predicate const & var) 
  {
    return ctx.read_value( var );
  }

  template <typename SolverType>
  result_wrapper 
  read_value(
      DirectSolver_Context<SolverType> & ctx
    , typename DirectSolver_Context<SolverType>::result_type var) 
  {
    return ctx.read_value( var );
  }

} // namespace metaSMT 

//  vim: ft=cpp:ts=2:sw=2:expandtab
