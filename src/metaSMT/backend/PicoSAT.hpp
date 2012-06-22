#pragma once

#include "../tags/SAT.hpp"
#include "../result_wrapper.hpp"

extern "C"
{
#include <picosat.h>
}
#include <vector>
#include <exception>

#include <boost/fusion/sequence/intrinsic.hpp>
#include <boost/fusion/support/is_sequence.hpp>
#include <boost/variant.hpp>
#include <boost/any.hpp> 
#include <boost/foreach.hpp>
 

namespace metaSMT {
  namespace solver {

    class PicoSAT
    {
      public:
        PicoSAT ()
        {
//          if ( in_use == USED )
//            throw std:runtime_error ("Picosat already in use. Only single instances supported."); 
         
          picosat_init (); 
//          in_use = USED;
        }

        ~PicoSAT ()
        {
          picosat_reset (); 
 //         in_use = UNUSED;
        }
         

        int toLit ( SAT::tag::lit_tag lit )
        {
          return lit.id; 
        }

        void clause ( std::vector < SAT::tag::lit_tag > const& clause)
        {
          BOOST_FOREACH ( SAT::tag::lit_tag const& lit, clause )
            picosat_add ( toLit ( lit ) );
          picosat_add ( 0 ); 
        }


        void assertion ( SAT::tag::lit_tag lit )
        {
          picosat_add ( toLit ( lit ) ); 
          picosat_add ( 0 ); 
        }

        void assumption ( SAT::tag::lit_tag lit )
        {
          picosat_assume ( toLit ( lit ) ); 
        }


        bool solve ( )
        {
          switch (picosat_sat (-1))
          {
            case PICOSAT_UNSATISFIABLE:
              return false;
            case PICOSAT_SATISFIABLE:
              return true;
            case PICOSAT_UNKNOWN:
              throw std::runtime_error ( "unknown return type of picosat_sat "); 
            default:
              throw std::runtime_error ( "unsupported return type of picosat_sat "); 
          }
        }

        result_wrapper read_value ( SAT::tag::lit_tag lit ) 
        {
           
          switch ( picosat_deref ( toLit ( lit ) ) )
          {
            case -1:
              return result_wrapper ( '0' );
            case 1:
              return result_wrapper ( '1' );
            case 0:
              return result_wrapper ( 'X' );
            default:
              std::cerr << "Unknown result." << std::endl;
              return result_wrapper ( 'X' ); 
          }
        }

      private:
//         enum { UNUSED, USED }; 
//         static int in_use = UNUSED; 
    };
  } /* solver */
} /* metaSMT */
// vim: ts=2 sw=2 et
