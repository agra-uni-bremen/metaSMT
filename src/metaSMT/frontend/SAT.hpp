#pragma once
#include "../tags/SAT.hpp"
#include "../transform/rewrite.hpp"
#include <boost/proto/core.hpp>
#include <boost/proto/transform.hpp>

// debug includes
#include <cstdio>
#include <boost/proto/debug.hpp>
#include <boost/mpl/int.hpp> 

namespace metaSMT {
   namespace SAT {
     namespace proto=boost::proto;
     
    /*** SAT/clase grammar ***/
    struct SAT_Domain;

    struct Literal
    : proto::or_<
        proto::terminal< tag::lit_tag >
      , proto::unary_expr< tag::not_tag, Literal>
      , proto::complement< Literal >
      , proto::logical_not< Literal >
    > {};


    struct SAT_Grammar 
		: proto::or_<
      proto::_,
        Literal
      , proto::plus<SAT_Grammar, SAT_Grammar>
      , proto::nary_expr<tag::c_tag, proto::vararg<SAT_Grammar> >
    > {};


    /*** SAT expression and Domain ***/ 
    template<typename Expr>
    struct SAT_Expr;

    struct SAT_Domain
    : proto::domain<proto::generator<SAT_Expr>, SAT_Grammar>
    {};

    template<typename Expr>
      struct SAT_Expr
      : proto::extends<Expr, SAT_Expr<Expr>, SAT_Domain >
      {
        typedef proto::extends<Expr, SAT_Expr<Expr>, SAT_Domain > base_type;

        SAT_Expr(Expr expr ) 
          : base_type(expr)
        {
        }
        SAT_Expr( ) 
          : base_type(Expr())
        {
        }
      };




     typedef 
     proto::result_of::make_expr< proto::tag::terminal, SAT_Domain
       , tag::lit_tag
     > ::type variable;

     variable new_variable() { 
        static unsigned _id = 0;
        ++_id;
        tag::lit_tag tag;
        tag.id = _id;
        return proto::make_expr< proto::tag::terminal, SAT_Domain >( tag );
     }
    
     struct clause {
     };
      
   } /* SAT */
} /* metaSMT */


// vim: tabstop=2 shiftwidth=2 expandtab
