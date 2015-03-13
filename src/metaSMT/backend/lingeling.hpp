#pragma once

#include "../tags/SAT.hpp"
#include "../result_wrapper.hpp"
#include "../Features.hpp"

extern "C"
{
#include <lglib.h>
}
#include <vector>
#include <exception>
#include <iostream>

#include <boost/fusion/sequence/intrinsic.hpp>
#include <boost/fusion/support/is_sequence.hpp>
#include <boost/variant.hpp>
#include <boost/any.hpp>
#include <boost/foreach.hpp>


namespace metaSMT {
  // Forward declaration
  struct addclause_cmd;
  namespace features
  {
    struct addclause_api;
  }

  namespace solver {
    class Lingeling
    {
      public:
        typedef SAT::tag::lit_tag result_type;

        Lingeling ()
        {
        }

        ~Lingeling ()
        {
        }


        int toLit ( result_type lit )
        {
          return lit.id;
        }

        void clause ( std::vector < result_type > const& clause)
        {
          BOOST_FOREACH ( result_type const& lit, clause )
            Lingeling_add ( toLit ( lit ) );
          Lingeling_add ( 0 );
        }

        void command ( addclause_cmd const&, std::vector < result_type > const& cls )
        {
          clause ( cls );
        }


        void assertion ( result_type lit )
        {
          Lingeling_add ( toLit ( lit ) );
          Lingeling_add ( 0 );
        }

        void assumption ( result_type lit )
        {
          Lingeling_assume ( toLit ( lit ) );
        }


        bool solve ( )
        {
          switch (Lingeling_sat (-1))
          {
            case Lingeling_UNSATISFIABLE:
              return false;
            case Lingeling_SATISFIABLE:
              return true;
            case Lingeling_UNKNOWN:
              throw std::runtime_error ( "unknown return type of Lingeling_sat ");
            default:
              throw std::runtime_error ( "unsupported return type of Lingeling_sat ");
          }
        }

        result_wrapper read_value ( result_type lit )
        {

          switch ( Lingeling_deref ( toLit ( lit ) ) )
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

  namespace features {
    template<>
      struct supports< solver::Lingeling, features::addclause_api>
      : boost::mpl::true_ {};
  } /* features */

} /* metaSMT */
// vim: ts=2 sw=2 et
