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
 
#include "../support/disable_warnings.hpp"

#include <minisat/core/Solver.h>

#include "../support/enable_warnings.hpp"


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
        typedef SAT::tag::lit_tag result_type;

        Minisat::Lit toLit ( result_type lit )
        {
          while ( solver_.nVars() <= abs ( lit.id ) )
            solver_.newVar();

          return Minisat::mkLit ( abs ( lit.id ), lit.id < 0 ); 
        }

        void clause ( std::vector < result_type > const& clause)
        {
          const size_t s = clause.size(); 
           
           // BOOST_FOREACH ( result_type const& lit, clause )
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


        void assertion ( result_type lit )
        {
          solver_.addClause ( toLit ( lit ) ); 
        }

        void assumption ( result_type lit )
        {
          assumption_.push ( toLit ( lit ) ); 
        }

        void command ( addclause_cmd const&, std::vector < result_type > const& cls )
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

        result_wrapper read_value ( result_type lit ) 
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
