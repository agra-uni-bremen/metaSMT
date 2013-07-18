
#pragma once

#include "../tags/Logic.hpp" 

#include <boost/any.hpp>

extern "C" {
#include <aiger.h>
}

namespace metaSMT 
{
  class Aiger  
  {
    public:
      typedef unsigned result_type;
      
      aiger *aig; 

    public:
      Aiger () : aig (aiger_init()) {} 
      ~Aiger () 
      {
        aiger_reset ( aig ); 
      }

      result_type operator() (logic::tag::var_tag const& var, boost::any args)
      {
        return new_var(); 
      }

      result_type operator() (logic::tag::true_tag const& , boost::any args)
      {
        return aiger_true;
      }
       
      result_type operator() (logic::tag::false_tag const& , boost::any args)
      {
        return aiger_false; 
      }

      result_type operator() (logic::tag::not_tag const&, result_type operand)
      {
        return aiger_not ( operand );
      }

      result_type operator() (logic::tag::and_tag const&, result_type lhs, result_type rhs )
      {
        result_type t = new_var();
        aiger_add_and ( aig, t, lhs, rhs );
        return t; 
      }

      result_type operator() (logic::tag::nand_tag const&, result_type lhs, result_type rhs )
      {
        result_type t = new_var();
        aiger_add_and ( aig, t, lhs, rhs );
        return aiger_not ( t );
      }

      result_type operator() (logic::tag::equal_tag const&, result_type lhs, result_type rhs )
      {
        return aiger_add_xnor ( aig, lhs, rhs ); 
      }

      result_type operator() (logic::tag::nequal_tag const&, result_type lhs, result_type rhs )
      {
        return aiger_not ( aiger_add_xnor ( aig, lhs, rhs ) ); 
      }

      result_type operator() (logic::tag::distinct_tag const&, result_type lhs, result_type rhs )
      {
        return aiger_not ( aiger_add_xnor ( aig, lhs, rhs ) ); 
      }

      result_type operator() (logic::tag::xnor_tag const&, result_type lhs, result_type rhs )
      {
        return aiger_add_xnor ( aig, lhs, rhs ); 
      }

      result_type operator() (logic::tag::implies_tag const&, result_type lhs, result_type rhs )
      {
        return aiger_add_or ( aig, aiger_not (lhs), rhs ); 
      }

      result_type operator() (logic::tag::or_tag const&, result_type lhs, result_type rhs )
      {
        return aiger_add_or ( aig, lhs, rhs ); 
      }
      
      result_type operator() (logic::tag::nor_tag const&, result_type lhs, result_type rhs )
      {
        return aiger_not ( aiger_add_or ( aig, lhs, rhs ) );
      }

      result_type operator() (logic::tag::xor_tag const&, result_type lhs, result_type rhs )
      {
        return aiger_add_xor ( aig, lhs, rhs ); 
      }

      result_type operator() (logic::tag::ite_tag const&, result_type I, result_type T, result_type E)
      {
        return aiger_add_ite ( aig, I, T, E );
      }


      template<typename T>
        result_type operator() (T const& , result_type lhs, result_type rhs )
        {
          assert ( false ); 
          return aiger_false; 
        }

      template<typename T, typename Arg>
        result_type operator() (T const& var, Arg lhs )
        {
          assert ( false ); 
          return aiger_false; 
        }

      template<typename T>
        result_type operator() (T const& var, result_type op1, result_type op2, result_type op3  )
        {
          assert ( false ); 
          return aiger_false; 
        }

      unsigned new_var ()
      {
        ++aig->maxvar;
        return aiger_var2lit( aig->maxvar );
      }
       
      unsigned aiger_add_or ( aiger *aig, unsigned lhs, unsigned rhs )
      {
        result_type t = new_var ();
        aiger_add_and ( aig, t, aiger_not (lhs), aiger_not (rhs) ); 
        return aiger_not ( t );  
      }

      unsigned aiger_add_xor ( aiger *aig, unsigned lhs, unsigned rhs )
      {
        return aiger_not ( aiger_add_xnor ( aig, lhs, rhs ) );
      }

      unsigned aiger_add_xnor ( aiger *aig, unsigned lhs, unsigned rhs )
      {
        result_type t1 = new_var ();
        result_type t2 = new_var ();

        aiger_add_and ( aig, t1, aiger_not ( lhs ), aiger_not ( rhs ) ); 
        aiger_add_and ( aig, t2, lhs, rhs ); 

        return aiger_add_or ( aig, t1, t2 ); 
      }

      unsigned aiger_add_ite ( aiger *aig, unsigned I, unsigned T, unsigned E )
      {
        result_type t = new_var (); 
        aiger_add_and ( aig 
            , t
            , aiger_add_or ( aig, aiger_not (I), T )
            , aiger_add_or ( aig, I, E ) );
        return t;
      }
  }; 


}
