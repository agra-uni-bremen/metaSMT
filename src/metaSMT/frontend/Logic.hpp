#pragma once
#include "../tags/Logic.hpp"
#include "../impl/_var_id.hpp"
#include <boost/functional/hash.hpp>
#include <boost/proto/core.hpp>

namespace proto=boost::proto;

namespace metaSMT {
  namespace logic {
 
    struct Predicate_Grammar;

    struct Binary_Predicate 
    : proto::or_<
        proto::binary_expr<tag::equal_tag, Predicate_Grammar, Predicate_Grammar>
      , proto::binary_expr<tag::nequal_tag, Predicate_Grammar, Predicate_Grammar>
    > {};

    // real Grammar
    struct Predicate_Grammar 
    : proto::and_<
        proto::not_< proto::address_of< proto::_> >
      , proto::not_< proto::equal_to< proto::_, proto::_ > >
      , proto::or_<
          proto::terminal< tag::true_tag >
        , proto::terminal< tag::false_tag >
        , Binary_Predicate
        , proto::_   // any other grammar
      >
    > {};

    template<typename Expr>
    struct Predicate;

    struct Predicate_Domain
    : proto::domain<proto::generator<Predicate>, Predicate_Grammar>
    {};

    template<typename Expr>
      struct Predicate
      : proto::extends<Expr, Predicate<Expr>, Predicate_Domain >
      {
        typedef proto::extends<Expr, Predicate<Expr>, Predicate_Domain > base_type;

        Predicate(Expr const & expr = Expr()) 
          : base_type(expr)
        {
        }
      };

    template<typename Expr> 
    void check (Predicate<Expr> const & ) {
      BOOST_MPL_ASSERT((proto::matches<Expr, Predicate_Grammar>));
    }
    template<typename Expr> 
    void check_not (Predicate<Expr> const & ) {
      BOOST_MPL_ASSERT_NOT((proto::matches<Expr, Predicate_Grammar>));
    }

   /** 
    * @ingroup Frontend
    * @defgroup Core Core Logic Frontend
    * @{
    */

    // expressions
    Predicate<proto::terminal<tag::true_tag>::type  > const True; // = {{{}}};
    Predicate<proto::terminal<tag::false_tag>::type > const False; // = {{{}}};

/** @cond */ 
 #define _BINARY_PREDICATE(NAME_, TAG_) \
      template<typename E1, typename E2> \
      typename proto::result_of::make_expr< TAG_, Predicate_Domain, E1 const &, E2 const & >::type \
      NAME_( E1 const& e1, E2 const & e2 ) \
      { \
        return proto::make_expr< TAG_, Predicate_Domain >(boost::cref(e1), boost::cref(e2));\
      } 
/** @endcond */

      _BINARY_PREDICATE(equal,   tag::equal_tag)
      _BINARY_PREDICATE(nequal,  tag::nequal_tag)
      _BINARY_PREDICATE(implies, tag::implies_tag)
      _BINARY_PREDICATE(And,     tag::and_tag)
      _BINARY_PREDICATE(Nand,    tag::nand_tag)
      _BINARY_PREDICATE(Or,      tag::or_tag)
      _BINARY_PREDICATE(Nor,     tag::nor_tag)
      _BINARY_PREDICATE(Xor,     tag::xor_tag)
      _BINARY_PREDICATE(Xnor,    tag::xnor_tag)
#undef _BINARY_PREDICATE

      template<typename E1, typename E2, typename E3>
      typename proto::result_of::make_expr< tag::ite_tag, Predicate_Domain, 
          E1 const &, E2 const &, E3 const & 
      >::type
      Ite( E1 const& e1, E2 const & e2 , E3 const & e3) 
      { 
        return proto::make_expr< tag::ite_tag, Predicate_Domain >(boost::cref(e1), boost::cref(e2), boost::cref(e3) );
      } 

      typedef 
      proto::result_of::make_expr< proto::tag::terminal, Predicate_Domain
        , tag::var_tag
      > ::type predicate;

    

      inline predicate 
      new_variable( )
      {
        tag::var_tag tag;
        tag.id = impl::new_var_id();
        return proto::make_expr< proto::tag::terminal, Predicate_Domain >( tag );
      } 

      inline std::size_t hash_value( predicate const &p ) {
        tag::var_tag const tag = boost::proto::value(p);
        std::size_t seed = 0;
        boost::hash_combine(seed, tag.id);
        return seed;
      }

      inline bool operator==( predicate const &lhs, predicate const &rhs ) {
        return proto::value(lhs).id == proto::value(rhs).id;
      }

      template<typename E1>
      typename proto::result_of::make_expr< 
          tag::not_tag, Predicate_Domain, E1 const &
        >::type
      Not( E1 const& e1 ) { 
        return proto::make_expr< tag::not_tag, Predicate_Domain >(
            boost::cref(e1) );
      } 

      template<typename E1, typename E2, typename E3>
      typename proto::result_of::make_expr< 
          tag::ite_tag
        , Predicate_Domain
        , E1 const &, E2 const &, E3 const &
        >::type
      implies( E1 const& e1, E2 const & e2, E3 const & e3 ) { 
        return proto::make_expr< tag::ite_tag, Predicate_Domain >(
            boost::cref(e1), boost::cref(e2), boost::cref(e3) 
        );
      }

   /**@}*/

  }// namespace logic

}// namespace metaSMT
	
//  vim: ft=cpp:ts=2:sw=2:expandtab
