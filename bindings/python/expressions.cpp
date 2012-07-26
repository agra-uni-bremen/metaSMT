#include <metaSMT/expression/default_visitation_unrolling_limit.hpp>
#include <metaSMT/expression/expression.hpp>
#include <metaSMT/expression/print_expression.hpp>
#include <metaSMT/support/DefaultSymbolTable.hpp>

#include <boost/python.hpp>
#include <boost/foreach.hpp>
#include <boost/format.hpp>
#include <boost/mpl/vector/vector50.hpp>
#include <boost/python/stl_iterator.hpp>
#include <boost/range/adaptors.hpp>
#include <boost/range/algorithm_ext/push_back.hpp>
#include <boost/range/iterator_range.hpp>

using namespace boost::python;

using namespace metaSMT::expression;

template<typename T>
logic_expression make_logic_expression( const T& v )
{
  return logic_expression( v );
}

logic_expression make_bit0()
{
  return logic_expression( metaSMT::logic::QF_BV::bit0 );
}

logic_expression make_bit1()
{
  return logic_expression( metaSMT::logic::QF_BV::bit1 );
}

logic_expression make_uint_expression( unsigned long value, unsigned long width )
{
  return bv_const<metaSMT::logic::QF_BV::tag::bvuint_tag>( value, width );
}

logic_expression make_sint_expression( long value, unsigned long width )
{
  return bv_const<metaSMT::logic::QF_BV::tag::bvsint_tag>( value, width );
}

logic_expression make_bin_expression( const std::string& value )
{
  return bv_const<metaSMT::logic::QF_BV::tag::bvbin_tag>::bin( value );
}

logic_expression make_hex_expression( const std::string& value )
{
  return bv_const<metaSMT::logic::QF_BV::tag::bvhex_tag>::hex( value );
}

logic_expression make_store_expression(const logic_expression &array,
        const logic_expression &index, const logic_expression &value)
{
  return store_expression(array, index, value);
}

logic_expression make_select_expression(const logic_expression &array,
        const logic_expression &index)
{
  return select_expression(array, index);
}

template<typename LogicTag, typename OpTag>
logic_expression make_unary_expression( const logic_expression& expr )
{
  return logic_expression( unary_expression<LogicTag, OpTag>( expr ) );
}

template<typename LogicTag, typename OpTag>
logic_expression make_binary_expression( const logic_expression& lhs, const logic_expression& rhs )
{
  return logic_expression( binary_expression<LogicTag, OpTag>( lhs, rhs ) );
}

template<typename LogicTag, typename OpTag>
logic_expression make_ternary_expression( const logic_expression& expr1, const logic_expression& expr2, const logic_expression& expr3 )
{
  return logic_expression( ternary_expression<LogicTag, OpTag>( expr1, expr2, expr3 ) );
}

template<typename LogicTag, typename OpTag>
logic_expression make_nary_expression( boost::python::list const& exprns )
{
  unsigned length ( boost::python::len(exprns) );
  std::vector<logic_expression> args;
  for (unsigned i = 0; i < length; ++i) {
    args.push_back( boost::python::extract<logic_expression>( exprns[i] ) );
  }
  return logic_expression( nary_expression<LogicTag, OpTag>( args ) );
}

template<typename T>
logic_expression make_extend_expression( unsigned long by, const logic_expression& expr )
{
  return logic_expression( extend_expression<T>( by, expr ) );
}

template<typename T>
logic_expression make_extract_expression( unsigned long from, unsigned long width, const logic_expression& expr )
{
  return logic_expression( extract_expression<T>( from, width, expr ) );
}

unsigned py_bitvector_width( const metaSMT::logic::QF_BV::bitvector& var )
{
  metaSMT::logic::QF_BV::tag::var_tag tag = boost::proto::value( var );
  return tag.width;
}

struct type_visitor : public boost::static_visitor<unsigned>
{
  unsigned operator()( bool expr ) const
  {
    return 0u;
  }

  unsigned operator()( const metaSMT::logic::QF_BV::QF_BV<boost::proto::terminal<metaSMT::logic::QF_BV::tag::bit0_tag>::type>& ) const
  {
    return 1u;
  }

  unsigned operator()( const metaSMT::logic::QF_BV::QF_BV<boost::proto::terminal<metaSMT::logic::QF_BV::tag::bit1_tag>::type>& ) const
  {
    return 1u;
  }

  unsigned operator()( const metaSMT::logic::predicate& pred ) const
  {
    return 0u;
  }

  unsigned operator()( const metaSMT::logic::QF_BV::bitvector& bv ) const
  {
    return 1u;
  }

  template<typename T>
  unsigned operator()( const bv_const<T>& expr ) const
  {
    return 1u;
  }

  template<typename Tag>
  unsigned operator()( const unary_expression<logic_tag, Tag>& expr ) const
  {
    return 0u;
  }

  template<typename Tag>
  unsigned operator()( const unary_expression<bv_tag, Tag>& expr ) const
  {
    return 1u;
  }

  template<typename Tag>
  unsigned operator()( const binary_expression<logic_tag, Tag>& expr ) const
  {
    return 0u;
  }

  template<typename Tag>
  unsigned operator()( const binary_expression<bv_tag, Tag>& expr ) const
  {
    return 1u;
  }

  template<typename Tag>
  unsigned operator()( const ternary_expression<logic_tag, Tag>& expr ) const
  {
    return 0u;
  }

  template<typename Tag>
  unsigned operator()( const ternary_expression<bv_tag, Tag>& expr ) const
  {
    return 1u;
  }

  template<typename Tag>
  unsigned operator()( const extend_expression<Tag>& expr ) const
  {
    return 1u;
  }

  template<typename Tag>
  unsigned operator()( const extract_expression<Tag>& expr ) const
  {
    return 1u;
  }

  template<typename T>
  unsigned operator()( T const & expr ) const
  {
    return (unsigned) -1;
  }

  unsigned operator()( const metaSMT::logic::Array::array &expr ) const
  {
    return 2u;
  }

  unsigned operator()( const store_expression &expr ) const
  {
    return 2u;
  }

  unsigned operator()( const select_expression &expr ) const
  {
    return 1u;
  }
};

unsigned py_logic_expression_type( const logic_expression& expr )
{
  return boost::apply_visitor( type_visitor(), expr );
}

std::string py_logic_expression_repr (logic_expression const& le) {
  std::ostringstream buf;
  std::ostream_iterator<char> ite(buf);
  metaSMT::expression::print_expression_static( ite, le, metaSMT::support::default_symbol_table);
  return buf.str();
}

void export_expressions()
{
  using namespace metaSMT::logic;

  class_<logic_expression>( "logic_expression" )
    .def( "type", &py_logic_expression_type )
    .def( "__repr__", &py_logic_expression_repr )
    ;
  def( "py_array_store", &make_store_expression );
  def( "py_array_select", &make_select_expression );
//  def( "py_new_array", &make_new_array );

  def( "py_logic_term", &make_logic_expression<bool> );
  def( "py_bv_bit0", &make_bit0 );
  def( "py_bv_bit1", &make_bit1 );
  def( "py_logic_predicate", &make_logic_expression<metaSMT::logic::predicate> );
  def( "py_logic_bv", &make_logic_expression<metaSMT::logic::QF_BV::bitvector> );
  def( "py_logic_array", &make_logic_expression<metaSMT::logic::Array::array> );

  def( "py_bv_uint", &make_uint_expression );
  def( "py_bv_sint", &make_sint_expression );
  def( "py_bv_bin" , &make_bin_expression );
  def( "py_bv_hex" , &make_hex_expression );

  def( "py_logic_not"    , &make_unary_expression<logic_tag, tag::not_tag> );
  def( "py_bv_not"       , &make_unary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvnot_tag> );
  def( "py_bv_neg"       , &make_unary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvneg_tag> );

  def( "py_logic_equal"  , &make_binary_expression<logic_tag, tag::equal_tag> );
  def( "py_logic_nequal" , &make_binary_expression<logic_tag, tag::nequal_tag> );
  def( "py_logic_implies", &make_binary_expression<logic_tag, tag::implies_tag> );
  def( "py_logic_and"    , &make_nary_expression<logic_tag, tag::and_tag> );
  def( "py_logic_nand"   , &make_binary_expression<logic_tag, tag::nand_tag> );
  def( "py_logic_or"     , &make_nary_expression<logic_tag, tag::or_tag> );
  def( "py_logic_nor"    , &make_binary_expression<logic_tag, tag::nor_tag> );
  def( "py_logic_xor"    , &make_binary_expression<logic_tag, tag::xor_tag> );
  def( "py_logic_xnor"   , &make_binary_expression<logic_tag, tag::xnor_tag> );

  def( "py_bv_and"     , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvand_tag> );
  def( "py_bv_nand"    , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvnand_tag> );
  def( "py_bv_or"      , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvor_tag> );
  def( "py_bv_nor"     , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvnor_tag> );
  def( "py_bv_xor"     , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvxor_tag> );
  def( "py_bv_xnor"    , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvxnor_tag> );

  def( "py_bv_add"     , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvadd_tag> );
  def( "py_bv_mul"     , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvmul_tag> );
  def( "py_bv_sub"     , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvsub_tag> );
  def( "py_bv_sdiv"    , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvsdiv_tag> );
  def( "py_bv_srem"    , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvsrem_tag> );
  def( "py_bv_udiv"    , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvudiv_tag> );
  def( "py_bv_urem"    , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvurem_tag> );

  def( "py_bv_shl"     , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvshl_tag> );
  def( "py_bv_shr"     , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvshr_tag> );
  def( "py_bv_ashr"    , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvashr_tag> );

  def( "py_bv_comp"    , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::bvcomp_tag> );
  def( "py_bv_slt"     , &make_binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvslt_tag> );
  def( "py_bv_sgt"     , &make_binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvsgt_tag> );
  def( "py_bv_sle"     , &make_binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvsle_tag> );
  def( "py_bv_sge"     , &make_binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvsge_tag> );
  def( "py_bv_ult"     , &make_binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvult_tag> );
  def( "py_bv_ugt"     , &make_binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvugt_tag> );
  def( "py_bv_ule"     , &make_binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvule_tag> );
  def( "py_bv_uge"     , &make_binary_expression<logic_tag, metaSMT::logic::QF_BV::tag::bvuge_tag> );

  def( "py_concat"     , &make_binary_expression<bv_tag, metaSMT::logic::QF_BV::tag::concat_tag> );
  def( "py_extract"    , &make_extract_expression<metaSMT::logic::QF_BV::tag::extract_tag> );
  def( "py_zero_extend", &make_extend_expression<metaSMT::logic::QF_BV::tag::zero_extend_tag> );
  def( "py_sign_extend", &make_extend_expression<metaSMT::logic::QF_BV::tag::sign_extend_tag> );

  def( "py_logic_ite"    , &make_ternary_expression<logic_tag, tag::ite_tag> );

  class_<metaSMT::logic::predicate>( "predicate" )
    ;
  def( "new_variable", &metaSMT::logic::new_variable );

  class_<metaSMT::logic::QF_BV::bitvector>( "bitvector" )
    .def( "width", &py_bitvector_width )
    ;
  def( "new_bitvector", &metaSMT::logic::QF_BV::new_bitvector );

  class_<metaSMT::logic::Array::array>( "array" )
      /* def index_width */
      /* def value_width */
    ;
  def( "new_array", &metaSMT::logic::Array::new_array );
}
