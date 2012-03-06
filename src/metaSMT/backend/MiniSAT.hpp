#pragma once

#include "../tags/SAT.hpp"
#include "../result_wrapper.hpp"
#include "../Features.hpp" 

 
#include <vector>
#include <iostream>
 
#include <boost/fusion/sequence/intrinsic.hpp>
#include <boost/fusion/support/is_sequence.hpp>
#include <boost/variant.hpp>
#include <boost/any.hpp> 
#include <boost/foreach.hpp>
 
/* disable MiniSAT warnings in GCC */
#pragma GCC push_options
#pragma GCC diagnostic ignored "-Wparentheses"

#include <minisat/core/Solver.h>

/* re-enable warnings */
#pragma GCC pop_options


namespace metaSMT {

  // Forward declaration
  struct addclause_cmd;
  namespace features
  {
    struct addclause_api;
  }
  namespace solver {

    class MiniSAT {

      public:
        Minisat::Lit toLit ( SAT::tag::lit_tag lit )
        {
          while ( solver_.nVars() <= abs ( lit.id ) )
            solver_.newVar();

          return Minisat::mkLit ( abs ( lit.id ), lit.id < 0 ); 
        }

        void clause ( std::vector < SAT::tag::lit_tag > const& clause)
        {
          const size_t s = clause.size(); 
           
           // BOOST_FOREACH ( SAT::tag::lit_tag const& lit, clause )
           //   std::cout << lit.id << " ";
           // std::cout << "0" << std::endl;

          switch ( s ) 
          {
            case 1:
              solver_.addClause ( toLit ( clause[0] ) ); 
              break;

            case 2:
              solver_.addClause ( toLit ( clause[0] ), toLit ( clause[1] ) ); 
              break;

            case 3:
              solver_.addClause ( toLit ( clause[0] )
                  , toLit ( clause[1] )
                  , toLit ( clause[2] ) ); 
              break; 

            default:
              {
                Minisat::vec<Minisat::Lit> v; 
                for (unsigned i = 0; i < s; ++i)
                {
                  v.push ( toLit ( clause[i] ) ); 
                }     
                solver_.addClause ( v ); 
                break; 
              }
          }
        }


        void assertion ( SAT::tag::lit_tag lit )
        {
          solver_.addClause ( toLit ( lit ) ); 
        }

        void assumption ( SAT::tag::lit_tag lit )
        {
          assumption_.push ( toLit ( lit ) ); 
        }

        void command ( addclause_cmd const&, std::vector < SAT::tag::lit_tag > const& cls )
        {
          clause ( cls );
        }


        bool solve ( )
        {
          solver_.simplify();
          if ( !solver_.okay()) {
            // might be unsat during pre-processing (empty clause derived)
            return false;
          }
           
          bool r = solver_.solve ( assumption_ ); 

          assumption_.clear (); 
          return r;
        }

        result_wrapper read_value ( SAT::tag::lit_tag lit ) 
        {
          using namespace Minisat;
           
          lbool val = solver_.modelValue (toLit(lit));
           
          if ( val == l_True )
            return result_wrapper ( '1' );
          else if ( val == l_False )
            return result_wrapper ( '0' );
           
          return result_wrapper ('X'); 
        }


      private:
        Minisat::Solver solver_;
        Minisat::vec<Minisat::Lit> assumption_;
    };
  } /* solver */

  namespace features {
    template<>
      struct supports< solver::MiniSAT, features::addclause_api>
      : boost::mpl::true_ {};
  } /* features */
} /* metaSMT */
// vim: ts=2 sw=2 et
