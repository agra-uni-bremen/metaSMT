
#pragma once

#include "Aiger.hpp"
#include "../tags/SAT.hpp"
#include "../Features.hpp"

#include <boost/foreach.hpp>
#include <vector>
#include <set>

namespace metaSMT
{
  // Forward declaration
  struct addclause_cmd;
  namespace features
  {
    struct addclause_api;
  }

  template<typename SatSolver>
  class SAT_Aiger
  {
    public:
      typedef Aiger::result_type result_type; 
       
    public:
      SAT_Aiger ()
      {
        true_var = aiger_lit2var ( aiger.new_var () );

        assertions.push_back ( true_var );

      }

      template< typename Command, typename Expr >
      void command ( Command& cmd, Expr& e )
      {
        solver.command ( cmd, e );
      }

      template<typename Tag, typename Any>
      result_type operator() (Tag const& tag, Any arg )
      {
        return aiger ( tag, arg ); 
      }
           
      template<typename T>
        result_type operator() (T const& tag, result_type lhs, result_type rhs )
        {
          return aiger ( tag, lhs, rhs );
        }

      template<typename T>
        result_type operator() (T const& tag, result_type lhs )
        {
          return aiger ( tag, lhs );
        }

      template<typename T>
        result_type operator() (T const& tag, result_type op1, result_type op2, result_type op3  )
        {
          return aiger ( tag, op1, op2, op3 ); 
        }

      void assertion ( result_type lit )
      {
        assertions.push_back ( lit ) ;
      }

      void assumption ( result_type lit )
      {
        assumptions.push_back ( lit ) ;
      }

      int sat_lit ( result_type lit )
      {
        if ( aiger_strip ( lit ) != 0 )
        {
          return aiger_sign ( lit ) ? -aiger_lit2var (lit) : aiger_lit2var ( lit );
        }
        else if ( aiger_true == lit )
          return true_var;
        else if ( aiger_false == lit )
          return -true_var;
         
        assert ( false ); 
        return aiger_false;
      }

      bool negated ( unsigned lit ) 
      {
        if ( lit == aiger_true )
          return false;
        else if ( lit == aiger_false )
          return true;
        return aiger_sign ( lit ); 
      }

      void _eval ( aiger_and const& and_sym ) 
      {
        unsigned lhs  = and_sym.lhs;
        unsigned rhs0 = and_sym.rhs0;
        unsigned rhs1 = and_sym.rhs1;

        if ( evaluated.find ( lhs ) == evaluated.end() )
        {
//           std::cout << "And: " << lhs << " " << rhs0 << " " << rhs1 << std::endl;
//           std::cout << "Sign: " << negated (lhs )<< " " << negated (rhs0) << " " << negated (rhs1) << std::endl;
         std::vector < SAT::tag::lit_tag > clause ( 2 );

         int lhsVar  = sat_lit ( lhs );
         int rhs0Var = sat_lit ( rhs0 );
         int rhs1Var = sat_lit ( rhs1 );

         clause[0].id = -lhsVar;
         clause[1].id =  rhs0Var;
         solver.clause ( clause );

         clause[1].id = rhs1Var;
         solver.clause ( clause );

         clause.resize ( 3 );
         clause[0].id = lhsVar; 
         clause[1].id = -rhs0Var;
         clause[2].id = -rhs1Var; 
         solver.clause ( clause );


          evaluated.insert ( lhs );
        }
      }

      bool solve () 
      {
        for (unsigned i = 0; i < aiger.aig->num_ands; i++)
        {
          _eval ( aiger.aig->ands[i] );
        }

        SAT::tag::lit_tag tmp;
        BOOST_FOREACH ( unsigned assertion, assertions )
        {
          tmp.id = sat_lit ( assertion ) ; 
          solver.assertion ( tmp ); 
        }

        BOOST_FOREACH ( unsigned assumption, assumptions )
        {
          tmp.id = sat_lit ( assumption ) ; 
          solver.assumption ( tmp  ); 
        }

        assumptions.clear(); 
        return solver.solve (); 
      }

      result_wrapper read_value ( result_type var ) 
      {
        SAT::tag::lit_tag lit = {  sat_lit ( var ) };
        return solver.read_value ( lit ); 
      }

    private:
      SatSolver solver;
      Aiger     aiger;

      std::vector < result_type > assertions; 
      std::vector < result_type > assumptions; 
      std::set < result_type >    evaluated;

      result_type true_var; 

  }; 

  namespace features {
    /* Stack supports stack api */
    template<typename Context>
    struct supports< SAT_Aiger<Context>, features::addclause_api>
    : boost::mpl::true_ {};

    /* Forward all other supported operations */
    template<typename Context, typename Feature>
    struct supports< SAT_Aiger<Context>, Feature>
    : supports<Context, Feature>::type {};
  }

}
