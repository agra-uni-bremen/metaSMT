#pragma once

#include "../support/SMT_Graph.hpp"
#include "../tags/QF_UF.hpp"
#include "../tags/Logics.hpp"
#include "../impl/_var_id.hpp"
#include "Logic.hpp"
#include <boost/proto/core.hpp>
#include <string>

namespace proto = boost::proto;

namespace metaSMT {

  namespace logic {

    namespace QF_UF {

      struct UninterpretedFunction_Grammar;

      // real Grammar
      struct UninterpretedFunction_Grammar
        : proto::and_<
            proto::not_< proto::equal_to< proto::_, proto::_ > >
	  , proto::or_<
	      proto::nary_expr<tag::function_var_tag, proto::vararg<proto::_> >
	  > >
      {};

      template <typename Expr>
      struct UninterpretedFunction;

      struct UninterpretedFunction_Domain
        : proto::domain<proto::generator<UninterpretedFunction>, UninterpretedFunction_Grammar>
      {};

      template <typename Expr>
      struct UninterpretedFunction
        : proto::extends<Expr, UninterpretedFunction<Expr>, UninterpretedFunction_Domain>
      {
        typedef proto::extends<Expr, UninterpretedFunction<Expr>, UninterpretedFunction_Domain> base_type;

        UninterpretedFunction(Expr const &expr = Expr())
          : base_type(expr)
        {}
      };

      template<typename Expr>
      void check (UninterpretedFunction<Expr> const & ) {
        BOOST_MPL_ASSERT((proto::matches<Expr, UninterpretedFunction_Grammar>));
      }

      template<typename Expr>
      void check_not (UninterpretedFunction<Expr> const & ) {
        BOOST_MPL_ASSERT_NOT((proto::matches<Expr, UninterpretedFunction_Grammar>));
      }

      typedef
      proto::result_of::make_expr< proto::tag::terminal, UninterpretedFunction_Domain
        , tag::function_var_tag
      > ::type Uninterpreted_Function;

      struct declare_function {
        declare_function(type::any_type t) {
          f_.id = impl::new_var_id();
          f_.result_type = t;
        }

        declare_function &operator()() {
          return *this;
        }

        declare_function &operator()(type::any_type a1) {
          f_.args.push_back( a1 );
          return *this;
        }

        declare_function &operator()(type::any_type a1, type::any_type a2) {
          f_.args.push_back( a1 );
          f_.args.push_back( a2 );
          return *this;
        }

        declare_function &operator()(type::any_type a1, type::any_type a2, type::any_type a3) {
          f_.args.push_back( a1 );
          f_.args.push_back( a2 );
          f_.args.push_back( a3 );
          return *this;
        }

        operator Uninterpreted_Function() {
	  return proto::make_expr< proto::tag::terminal, UninterpretedFunction_Domain >( f_ );
        }

        tag::function_var_tag f_;
      };

      bool operator==( Uninterpreted_Function const &lhs, Uninterpreted_Function const &rhs ) {
	tag::function_var_tag const lhs_tag = proto::value(lhs);
	tag::function_var_tag const rhs_tag = proto::value(rhs);
	if ( lhs_tag.id != rhs_tag.id ||
	     !(lhs_tag.result_type == rhs_tag.result_type) ||
	     lhs_tag.args.size() != rhs_tag.args.size() ) {
	  return false;
	}

	for (unsigned u = 0; u < lhs_tag.args.size(); ++u) {
	  if ( !(lhs_tag.args[u] == rhs_tag.args[u]) )
	    return false;
	}

	return true;
      }

      // replicate code above for more args
    } // namespace QF_UF
  } // namepace logic
} // namespace metaSMT

//  vim: ft=cpp:ts=2:sw=2:expandtab
