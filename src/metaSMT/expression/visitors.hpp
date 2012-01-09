#pragma once

#include <boost/variant/static_visitor.hpp>
#include <boost/format.hpp>

#include "expression.hpp"

namespace metaSMT {  
  namespace expression {
    // forward declarations
    template < typename Tag >
    bool has_type(logic_expression const &expr);

    bool is_constant(logic_expression const &expr);
    bool is_variable(logic_expression const &expr);
    bool is_simple(logic_expression const &expr);
    bool is_compound(logic_expression const &expr);

    unsigned char get_arity(logic_expression const &expr);

    bool has_const_value(logic_expression const &expr, unsigned long const &value);

    template < typename Tag >
    struct has_type_visitor : public boost::static_visitor< bool > {
      has_type_visitor() {}

      bool operator() ( Tag const & ) const {
	return true;
      }

      template < typename OtherTag >
      bool operator() ( OtherTag const & ) const {
	return false;
      }
    }; // has_type_visitor

    template < typename TagVector >
    struct has_type_from_list_visitor : public boost::static_visitor<bool> {
      has_type_from_list_visitor() {}

      template < typename Tag >
      typename boost::enable_if<
	boost::is_same<
	  typename boost::mpl::find<TagVector, Tag>
	, typename boost::mpl::end<TagVector>::type
	>
      , bool
      >
      ::type operator() ( Tag const & ) const {
	return true;
      }

      template < typename OtherTag >
      bool operator() ( OtherTag const & ) const {
	return false;
      }
    }; // has_type_from_list_visitor

    struct is_constant_visitor : public boost::static_visitor<bool> {
      is_constant_visitor() {}

      typedef boost::mpl::vector <
	bool
      , bit0_const
      , bit1_const
      , bv_const<bvtags::bvuint_tag>
      , bv_const<bvtags::bvsint_tag>
      , bv_const<bvtags::bvbin_tag>
      , bv_const<bvtags::bvhex_tag>
      > ConstantExpr;

      template < typename Tag >
      typename boost::enable_if<
        boost::is_same<
          typename boost::mpl::find<ConstantExpr, Tag>
        , boost::mpl::end<ConstantExpr>::type
        >
      , bool
      >
      ::type operator() ( Tag const & ) const {
        return true;
      }

      template < typename OtherTag >
      bool operator() ( OtherTag const & ) const {
	return false;
      }
    }; // is_constant_visitor

    struct has_const_value_visitor : public boost::static_visitor<bool> {
      has_const_value_visitor(unsigned long const &value)
	: value_(value)
      {}

      bool operator() ( bit0_const const & ) const {
	return (value_ == 0);
      }

      bool operator() ( bit1_const const & ) const {
	return (value_ == 1);
      }

      template < typename OpTag >
      bool operator() ( bv_const<OpTag> const &const_expr ) const {
	return (const_expr.value == value_ && !const_expr.overflow);
      }

      template < typename OtherTag >
      bool operator() ( OtherTag const & ) const {
	return false;
      }

      unsigned long const value_;
    }; // has_const_value_visitor

    struct is_variable_visitor : public boost::static_visitor<bool> {
      is_variable_visitor() {}

      typedef boost::mpl::vector <
	metaSMT::logic::predicate
      , metaSMT::logic::QF_BV::bitvector
      , metaSMT::logic::Array::array
      , metaSMT::logic::QF_UF::Uninterpreted_Function
      > VarExpr;

      template < typename Tag >
      typename boost::enable_if<
	boost::is_same<
	  typename boost::mpl::find<VarExpr, Tag>
	, boost::mpl::end<VarExpr>::type
	>
      , bool
      >
      ::type operator() ( Tag const & ) const {
	return true;
      }

      template < typename OtherTag >
      bool operator() ( OtherTag const & ) const {
	return false;
      }
    }; // is_variable_visitor

    struct get_arity_visitor : public boost::static_visitor<unsigned char> {
      get_arity_visitor() {}

      typedef boost::mpl::vector <
	bool
      , bit0_const
      , bit1_const
      , bv_const<bvtags::bvuint_tag>
      , bv_const<bvtags::bvsint_tag>
      , bv_const<bvtags::bvbin_tag>
      , bv_const<bvtags::bvhex_tag>
      > ZeroArityExpr;

      template < typename Tag >
      typename boost::enable_if<
	boost::is_same<
	  typename boost::mpl::find<ZeroArityExpr, Tag>
	, boost::mpl::end<ZeroArityExpr>::type
	>
      , unsigned char
      >
      ::type operator() ( Tag const & ) const {
	return 0;
      }

      // generic expression types
      template < typename ReturnTag, typename OpTag >
      unsigned char operator() ( unary_expression<ReturnTag, OpTag> const & ) const {
	return 1;
      }

      template < typename ReturnTag, typename OpTag >
      unsigned char operator() ( binary_expression<ReturnTag, OpTag> const & ) const {
	return 2;
      }

      template < typename ReturnTag, typename OpTag >
      unsigned char operator() ( ternary_expression<ReturnTag, OpTag> const & ) const {
	return 3;
      }

      // special expression types
      unsigned char operator() ( extract_expression<bvtags::extract_tag> const & ) const {
	return 1;
      }

      template < typename OpTag >
      unsigned char operator() ( extend_expression<OpTag> const & ) const {
	return 1;
      }

      unsigned char operator() ( select_expression const & ) const {
	return 2;
      }

      unsigned char operator() ( store_expression const & ) const {
	return 3;
      }

      template < typename OtherTag >
      unsigned char operator() ( OtherTag const & ) const {
	assert( false && "Type has no defined arity" );
	return 0;
      }
    }; // get_arity_visitor

    template < typename Tag >
    inline bool has_type(logic_expression const &expr) {
      return boost::apply_visitor( has_type_visitor<Tag>(), expr );
    }

    typedef boost::mpl::vector <
      bool
    , bit0_const
    , bit1_const
    , bv_const<bvtags::bvuint_tag>
    , bv_const<bvtags::bvsint_tag>
    , bv_const<bvtags::bvbin_tag>
    , bv_const<bvtags::bvhex_tag>
    > ConstantExpr;

    inline bool is_constant(logic_expression const &expr) {
      return boost::apply_visitor( has_type_from_list_visitor<ConstantExpr>(), expr );
    }

    typedef boost::mpl::vector <
      metaSMT::logic::predicate
    , metaSMT::logic::QF_BV::bitvector
    , metaSMT::logic::Array::array
    , metaSMT::logic::QF_UF::Uninterpreted_Function
    > VarExpr;

    inline bool is_variable(logic_expression const &expr) {
      return boost::apply_visitor( has_type_from_list_visitor<VarExpr>(), expr );
    }

    typedef boost::mpl::insert_range<
      ConstantExpr
    , boost::mpl::end<ConstantExpr>::type
    , VarExpr
    > SimpleExpr;

    inline bool is_simple(logic_expression const &expr) {
      return boost::apply_visitor( has_type_from_list_visitor<SimpleExpr>(), expr );
    }

    inline bool is_compound(logic_expression const &expr) {
      return !is_simple(expr);
    }

    inline unsigned char get_arity(logic_expression const &expr) {
      return boost::apply_visitor( get_arity_visitor(), expr );
    }

    inline bool has_const_value(logic_expression const &expr, unsigned long const &value) {
      return boost::apply_visitor( has_const_value_visitor(value), expr );
    }
  } // expression
} // metaSMT
