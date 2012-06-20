#ifndef EXPRESSIONS_HPP
#define EXPRESSIONS_HPP

#include <string>

#include <boost/mpl/vector/vector50.hpp>
#include <boost/proto/core.hpp>
#include <boost/variant.hpp>

#include <metaSMT/frontend/QF_BV.hpp>

namespace proto = boost::proto;
namespace tag = metaSMT::logic::tag;

namespace boost { namespace mpl {
#define BOOST_PP_ITERATION_PARAMS_1 \
    (3, (51, 60, "boost/mpl/vector/aux_/numbered.hpp"))
#include BOOST_PP_ITERATE()
}}

// frontend Logic
struct logic_tag {};
struct bv_tag {};

template<typename LogicTag, typename OpTag> struct unary_expression;
template<typename LogicTag, typename OpTag> struct binary_expression;
template<typename LogicTag, typename OpTag> struct ternary_expression;

template<typename OpTag> struct extend_expression;
template<typename OpTag> struct extract_expression;

struct bvuint_expression
{
  unsigned long value;
  unsigned long width;

  bvuint_expression( unsigned long value, unsigned long width ) : value( value ), width( width ) {}
};

struct bvsint_expression
{
  long value;
  unsigned long width;

  bvsint_expression( long value, unsigned long width ) : value( value ), width( width ) {}
};

template<typename OpTag>
struct bvstr_expression
{
  std::string value;

  bvstr_expression( const std::string& value ) : value( value ) {}
};

typedef boost::mpl::vector51<bool,
                             metaSMT::logic::QF_BV::QF_BV<boost::proto::terminal<metaSMT::logic::QF_BV::tag::bit0_tag>::type>,
                             metaSMT::logic::QF_BV::QF_BV<boost::proto::terminal<metaSMT::logic::QF_BV::tag::bit1_tag>::type>,
                             metaSMT::logic::predicate,
                             metaSMT::logic::QF_BV::bitvector,

                             bvuint_expression,
                             bvsint_expression,
                             bvstr_expression<metaSMT::logic::QF_BV::tag::bvbin_tag>,
                             bvstr_expression<metaSMT::logic::QF_BV::tag::bvhex_tag>,

                             boost::recursive_wrapper<unary_expression<logic_tag, tag::not_tag> >,

                             boost::recursive_wrapper<unary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvnot_tag> >,
                             boost::recursive_wrapper<unary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvneg_tag> >,

                             boost::recursive_wrapper<binary_expression<logic_tag, tag::equal_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, tag::nequal_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, tag::implies_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, tag::and_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, tag::nand_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, tag::or_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, tag::nor_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, tag::xor_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, tag::xnor_tag> >,

                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvand_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvnand_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvor_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvnor_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvxor_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvxnor_tag> >,

                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvadd_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvmul_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvsub_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvsdiv_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvsrem_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvudiv_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvurem_tag> >,

                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvshl_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvshr_tag> >,
                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvashr_tag> >,

                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvcomp_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvslt_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvsgt_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvsle_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvsge_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvult_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvugt_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvule_tag> >,
                             boost::recursive_wrapper<binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvuge_tag> >,

                             boost::recursive_wrapper<binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::concat_tag> >,
                             boost::recursive_wrapper<extract_expression<metaSMT::logic::QF_BV::tag::extract_tag> >,
                             boost::recursive_wrapper<extend_expression<metaSMT::logic::QF_BV::tag::zero_extend_tag> >,
                             boost::recursive_wrapper<extend_expression<metaSMT::logic::QF_BV::tag::sign_extend_tag> >,

                             boost::recursive_wrapper<ternary_expression<logic_tag, tag::ite_tag> > >::type logic_expression_types;

typedef boost::make_variant_over<logic_expression_types>::type logic_expression;

template<typename LogicTag, typename OpTag>
struct unary_expression
{
  logic_expression expr;

  unary_expression( const logic_expression& expr ) : expr( expr ) {}
};

template<typename LogicTag, typename OpTag>
struct binary_expression
{
  logic_expression left;
  logic_expression right;

  binary_expression( const logic_expression& lhs, const logic_expression& rhs ) : left( lhs ), right( rhs ) {}
};

template<typename LogicTag, typename OpTag>
struct ternary_expression
{
  logic_expression expr1;
  logic_expression expr2;
  logic_expression expr3;

  ternary_expression( const logic_expression& expr1, const logic_expression& expr2, const logic_expression& expr3 ) : expr1( expr1 ), expr2( expr2 ), expr3( expr3 ) {}
};

template<typename OpTag>
struct extend_expression
{
  unsigned long by;
  logic_expression expr;

  extend_expression( unsigned long by, const logic_expression& expr ) : by( by ), expr( expr ) {}
};

template<typename OpTag>
struct extract_expression
{
  unsigned long from;
  unsigned long width;
  logic_expression expr;

  extract_expression( unsigned long from, unsigned long width, const logic_expression& expr ) : from( from ), width( width ), expr( expr ) {}
};

void export_expressions();

#endif /* EXPRESSIONS_HPP */
