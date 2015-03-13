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
            m_solver = lglinit ();
        }

        ~Lingeling ()
        {
            lglrelease ( m_solver );
        }

        int toLit ( result_type lit )
        {
          return lit.id;
        }

        void clause ( std::vector < result_type > const& clause)
        {
          BOOST_FOREACH ( result_type const& lit, clause ) {
            add ( toLit ( lit ) );
          }

          add ( 0 );
        }

        void command ( addclause_cmd const&, std::vector < result_type > const& cls )
        {
          clause ( cls );
        }

        void assertion ( result_type lit )
        {
          add ( toLit ( lit ), 0 );
        }

        void assumption ( result_type lit )
        {
          m_buffered_assume_clauses.push_back( toLit ( lit ) );
        }

        void add ( int lit )
        {
          m_buffered_clauses.push_back( lit );
        }

        void add ( int lit0, int lit1 )
        {
          m_buffered_clauses.push_back( lit0 );
          m_buffered_clauses.push_back( lit1 );
        }

        void flush_buffered_clauses ()
        {
          BOOST_FOREACH ( int lit, m_buffered_clauses ) {
            if ( lit != 0 ) {
              lglfreeze ( m_solver, lit );
            }
            lgladd ( m_solver, lit );
          }

          m_buffered_clauses.clear();
        }

        void flush_buffered_assumptions () {
          BOOST_FOREACH( int lit, m_buffered_assume_clauses ){
              lglfreeze ( m_solver, lit );
              lglassume ( m_solver, lit );
          }

          m_buffered_assume_clauses.clear();;
        }

        bool solve ( )
        {
          flush_buffered_clauses();
          flush_buffered_assumptions();

          switch (lglsat (m_solver))
          {
            case LGL_UNSATISFIABLE:
              return false;
            case LGL_SATISFIABLE:
              return true;
            case LGL_UNKNOWN:
              throw std::runtime_error ( "unknown return type of Lingeling_sat ");
            default:
              throw std::runtime_error ( "unsupported return type of Lingeling_sat ");
          }
        }


        result_wrapper read_value ( result_type lit )
        {
          switch ( lglderef ( m_solver, toLit ( lit ) ) )
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
        LGL* m_solver;

        std::vector < int > m_buffered_clauses;
        std::vector < int > m_buffered_assume_clauses;
    };
  } /* solver */

  namespace features {
    template<>
      struct supports< solver::Lingeling, features::addclause_api>
      : boost::mpl::true_ {};
  } /* features */

} /* metaSMT */
// vim: ts=2 sw=2 et
