#pragma once

#include <boost/fusion/support/is_sequence.hpp>
#include <boost/fusion/include/distance.hpp>
#include <boost/fusion/algorithm/iteration/for_each.hpp>

#include <iostream>

namespace metaSMT {

  /**
   * @brief try to explain why a set of expressions is unsat
   * @ingroup unstable
   *
   * take a tuple of assumptions and try to isolate the reason why the tuple is
   * unsat
   * returns a vector<bool> of the same size, where each index is true when the
   * expressin at this index is part of the reason.
   **/
  template< typename Context, typename Tuple>
  std::vector<bool> why_unsat ( Context & ctx, Tuple t);

  /**
   * print the expressions that cause the expression to be unsat
   **/
  template< typename Context, typename Tuple>
  void print_why_unsat ( Context & ctx, Tuple t);

/******* implementation details *****/

  namespace impl {
    template<typename Solver>
    struct ConditionalAssumptionCaller {
      Solver & solver;
      vector<bool>::const_iterator & ite;
      ConditionalAssumptionCaller( Solver & solver, vector<bool>::const_iterator & ite ) 
        : solver( solver )
        , ite( ite )
      { }

      template< typename Expr >
      void operator() ( Expr e ) const {
        if ( *ite ) {
          assumption(solver, e);
        }
        ++ite;
      }
    };

    struct ConditionalPrinter {
      vector<bool>::const_iterator & ite;
      ConditionalPrinter( vector<bool>::const_iterator & ite ) 
        : ite( ite )
      { }

      template< typename Expr >
      void operator() ( Expr e ) const {
        if ( *ite ) {
          boost::proto::display_expr( e );
        }
        ++ite;
      }
    };
  } /* impl */

  /**
   * take a tuple of assumptions and try to isolate the reason why the tuple is unsat
   * returns a vector<bool> of the same size, where each index is true when the
   * expressin at this index is part of the reason.
   **/

  template< typename Context, typename Tuple>
  std::vector<bool> why_unsat ( Context & ctx, Tuple t) {
    using namespace boost::fusion;

    BOOST_MPL_ASSERT(( typename traits::is_sequence< Tuple >::type ));

    std::vector<bool> result (distance(begin(t),end(t)), true);

    // iterate lineary over result and drop one assumption at a time.
    // if problem is still unsat, keep it, otherwise set its position to true.
    // maybe re-iterate

    bool more = true;
  
    std::vector<bool>::iterator ite = result.begin();
    while(more) {
      more = false;
     
      // seach an expression not yet disabled
      for( ite = result.begin(); ite != result.end(); ++ite) {
        if ( !*ite) continue; // already disabled;

        // disable this expression for testing
        *ite=false;
        std::vector<bool>::const_iterator cond = result.begin();
        impl::ConditionalAssumptionCaller<Context> assumer( ctx, cond );
        for_each( t, assumer );

        if(!solve(ctx)) {
          more=true;
        } else {
          *ite = true;  
        }
      }
    }


    return result;

  }

  template< typename Context, typename Tuple>
  void print_why_unsat ( Context & ctx, Tuple t) {
    using namespace boost::fusion;

    BOOST_MPL_ASSERT(( typename traits::is_sequence< Tuple >::type ));

    std::vector<bool> result = why_unsat(ctx, t);

    std::vector<bool>::const_iterator cond = result.begin();
    impl::ConditionalPrinter printer( cond );
    for_each( t, printer );
  }



} /* metaSMT */

