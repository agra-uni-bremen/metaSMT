#pragma once
#include <string>
#include <bitset>

#include <boost/proto/core.hpp>
#include <boost/variant.hpp>
#include <boost/format.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>

#include <metaSMT/frontend/Logic.hpp>
#include <metaSMT/frontend/QF_BV.hpp>
#include <metaSMT/frontend/Array.hpp>
#include <metaSMT/frontend/QF_UF.hpp>
#include <metaSMT/support/SMT_Tag_Mapping.hpp>
#include <metaSMT/support/boost_mpl_vector60.hpp>

namespace metaSMT {
  namespace expression {
    namespace proto = boost::proto;
    namespace predtags = metaSMT::logic::tag;
    namespace bvtags = metaSMT::logic::QF_BV::tag;
    namespace arraytags = metaSMT::logic::Array::tag;
    namespace uftags = metaSMT::logic::QF_UF::tag;

    // return types
    struct logic_tag {};
    struct bv_tag {};
    struct uf_tag {};

    template< typename ReturnTag, typename OpTag >
    struct unary_expression;

    template< typename ReturnTag, typename OpTag >
    struct binary_expression;

    template< typename ReturnTag, typename OpTag >
    struct ternary_expression;

    template< typename ReturnTag, typename OpTag >
    struct nary_expression;

    template < typename OpTag >
    struct extract_expression;

    template < typename OpTag >
    struct extend_expression;

    template < typename OpTag >
    struct bv_const;

    template < typename OpTag >
    struct bv_const {
      unsigned long value;
      unsigned long width;
      std::string str;
      bool overflow;

      static bv_const<bvtags::bvhex_tag> hex(std::string const &hex_string) {
        //std::cerr << "hex " << hex_string << '\n';
        typedef std::string::const_iterator ConstIterator;
        ConstIterator it = hex_string.begin(), ie = hex_string.end();

        static boost::spirit::qi::rule< ConstIterator, unsigned long() > hex_rule
          = boost::spirit::qi::uint_parser<unsigned long, 16, 1, 16>()
          ;

        unsigned long value;
        if ( boost::spirit::qi::parse(it, ie, hex_rule, value) ) {
          assert( it == ie && "Expression not completely consumed" );
          unsigned const width = (hex_string.size() - 2)*4;
          return bv_const<bvtags::bvhex_tag>(value, width, hex_string);
        }

        assert( false && "Unable to parse hex literal" );
        throw std::exception();
      }

      static bv_const<bvtags::bvbin_tag> bin(std::string const &bin_string) {
        //std::cerr << "bin " << std::bitset<(sizeof(unsigned long)*8)>(bin_string).to_ulong() << '\n';
        return bv_const<bvtags::bvbin_tag>(
                 std::bitset<(sizeof(unsigned long)*8)>(bin_string).to_ulong(),
                 bin_string.size(),
                 bin_string
               );
      }

      bv_const( unsigned long value,
                unsigned long width,
                std::string const &str,
                bool valid = true)
        : value( value )
        , width( width )
        , str( str )
        , overflow( false )
      {
        unsigned long const max_width = sizeof(unsigned long)*8;
        if ( max_width <= width ) {
          overflow = true;
        }
        //std::cerr << "bv_const: (" << value << "," << width << "," << str << ")\n";
      }

      bv_const( unsigned long value,
                unsigned long width)
        : value( value )
        , width( width )
        , str( boost::str(boost::format("%u") % value) )
      {
        //std::cerr << "bv_const: (" << value << "," << width << "," << str << ")\n";
      }

      bool operator==( bv_const<OpTag> const &rhs ) const {
        return (value == rhs.value && width == rhs.width);
      }

      template < typename RHS >
      bool operator==( RHS const & ) const {
        return false;
      }

    }; // bv_const

    struct select_expression;
    struct store_expression;

    typedef metaSMT::logic::QF_BV::QF_BV<
      proto::terminal<bvtags::bit0_tag>::type
    > bit0_const;

    typedef metaSMT::logic::QF_BV::QF_BV<
      proto::terminal<bvtags::bit1_tag>::type
    > bit1_const;

    typedef boost::mpl::vector56<
      // constants
        bool
      , bit0_const
      , bit1_const
      , bv_const<bvtags::bvuint_tag>
      , bv_const<bvtags::bvsint_tag>
      , bv_const<bvtags::bvhex_tag>
      , bv_const<bvtags::bvbin_tag>

      // variables
      , metaSMT::logic::predicate
      , metaSMT::logic::QF_BV::bitvector
      , metaSMT::logic::Array::array
      , metaSMT::logic::QF_UF::Uninterpreted_Function

      // unary expressions
      , boost::recursive_wrapper<unary_expression<logic_tag, predtags::not_tag> >
      , boost::recursive_wrapper<unary_expression<bv_tag, bvtags::bvnot_tag> >
      , boost::recursive_wrapper<unary_expression<bv_tag, bvtags::bvneg_tag> >

      // binary expressions
      , boost::recursive_wrapper<binary_expression<logic_tag, predtags::equal_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, predtags::nequal_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, predtags::implies_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, predtags::nand_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, predtags::nor_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, predtags::xor_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, predtags::xnor_tag> >

      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvand_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvnand_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvor_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvnor_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvxor_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvxnor_tag> >

      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvadd_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvmul_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvsub_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvsdiv_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvsrem_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvudiv_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvurem_tag> >

      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvshl_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvshr_tag> >
      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvashr_tag> >

      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::bvcomp_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, bvtags::bvslt_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, bvtags::bvsgt_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, bvtags::bvsle_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, bvtags::bvsge_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, bvtags::bvult_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, bvtags::bvugt_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, bvtags::bvule_tag> >
      , boost::recursive_wrapper<binary_expression<logic_tag, bvtags::bvuge_tag> >

      , boost::recursive_wrapper<binary_expression<bv_tag, bvtags::concat_tag> >

      // ternary expressions
      , boost::recursive_wrapper<ternary_expression<logic_tag, predtags::ite_tag> >

      // nary expressions
      , boost::recursive_wrapper<nary_expression<uf_tag, proto::tag::function> >
      , boost::recursive_wrapper<nary_expression<logic_tag, predtags::and_tag> >
      , boost::recursive_wrapper<nary_expression<logic_tag, predtags::or_tag> >

      // expressions with special syntax
      , boost::recursive_wrapper<extract_expression<bvtags::extract_tag> >
      , boost::recursive_wrapper<extend_expression<bvtags::zero_extend_tag> >
      , boost::recursive_wrapper<extend_expression<bvtags::sign_extend_tag> >
      , boost::recursive_wrapper<select_expression>
      , boost::recursive_wrapper<store_expression>
    >::type logic_expression_types;

    typedef boost::make_variant_over<logic_expression_types>::type logic_expression;

    template < typename ReturnTag, typename OpTag >
    struct unary_expression {
      logic_expression expr;

      unary_expression( logic_expression const &expr )
        : expr( expr )
      {}

      bool operator==( unary_expression<ReturnTag, OpTag> const &rhs ) const {
        return (expr == rhs.expr);
      }

      template < typename RHS >
      bool operator==( RHS const & ) const {
        return false;
      }

      std::string const name() const {
        return get_tag_name(OpTag());
      }
    }; // unary_expression

    template < typename ReturnTag, typename OpTag >
    struct binary_expression {
      logic_expression left;
      logic_expression right;

      binary_expression( logic_expression const &lhs,
                         logic_expression const &rhs )
        : left( lhs )
        , right( rhs )
      {}

      bool operator==( binary_expression<ReturnTag, OpTag> const &rhs ) const {
        return boost::tie(left, right) == boost::tie(rhs.left, rhs.right);
      }

      template < typename RHS >
      bool operator==( RHS const & ) const {
        return false;
      }

      std::string const name() const {
        return get_tag_name(OpTag());
      }
    }; // binary_expression

    template < typename ReturnTag, typename OpTag >
    struct ternary_expression {
      logic_expression expr1;
      logic_expression expr2;
      logic_expression expr3;

      ternary_expression( logic_expression const &expr1,
                          logic_expression const &expr2,
                          logic_expression const &expr3 )
        : expr1( expr1 )
        , expr2( expr2 )
        , expr3( expr3 )
      {}

      bool operator==( ternary_expression<ReturnTag, OpTag> const &rhs ) const {
        return boost::tie(expr1, expr2, expr3) == boost::tie(rhs.expr1, rhs.expr2, rhs.expr3);
      }

      template < typename RHS >
      bool operator==( RHS const & ) const {
        return false;
      }

      std::string const name() const {
        return get_tag_name(OpTag());
      }
    }; // ternary_expression

    template < typename ReturnTag, typename OpTag >
    struct nary_expression {
      typedef std::vector< logic_expression > ContainerType;
      ContainerType exprs;

      nary_expression( ContainerType const &exprs )
        : exprs(exprs)
      {}

      bool operator==( nary_expression<ReturnTag, OpTag> const &rhs ) const {
        if ( exprs.size() != rhs.exprs.size() ) {
          return false;
        }

        for (unsigned u = 0; u < exprs.size(); ++u) {
          if ( !(exprs[u] == rhs.exprs[u]) ) {
            return false;
          }
        }

        return true;
      }

      template < typename RHS >
      bool operator==( RHS const & ) const {
        return false;
      }

      typename ContainerType::iterator begin() {
        return exprs.begin();
      }

      typename ContainerType::iterator end() {
        return exprs.end();
      }

      typename ContainerType::const_iterator begin() const {
        return exprs.begin();
      }

      typename ContainerType::const_iterator end() const {
        return exprs.end();
      }

      std::string const name() const {
        return get_tag_name(OpTag());
      }
    }; // nary_expression

    template < typename OpTag >
    struct extend_expression {
      unsigned long by;
      logic_expression expr;

      extend_expression( unsigned long by,
                         logic_expression const &expr )
        : by( by )
        , expr( expr )
      {}

      bool operator==( extend_expression const &rhs ) const {
        return boost::tie(by, expr) == boost::tie(rhs.by, rhs.expr);
      }

      template < typename RHS >
      bool operator==( RHS const & ) const {
        return false;
      }

    }; // extend_expression

    template < typename OpTag >
    struct extract_expression {
      unsigned long from;
      unsigned long width;
      logic_expression expr;

      extract_expression( unsigned long from,
                          unsigned long width,
                          logic_expression const &expr )
        : from( from )
        , width( width )
        , expr( expr )
      {}

      bool operator==( extract_expression const &rhs ) const {
        return boost::tie(from, width, expr) == boost::tie(rhs.from, rhs.width, rhs.expr);
      }

      template < typename RHS >
      bool operator==( RHS const & ) const {
        return false;
      }

    }; // extract_expression

    struct select_expression {
      logic_expression array;
      logic_expression index;

      select_expression( logic_expression const &array,
                         logic_expression const &index )
        : array( array )
        , index( index )
      {}

      bool operator==( select_expression const &rhs ) const {
        return boost::tie(array, index) == boost::tie(rhs.array, rhs.index);
      }

      template < typename RHS >
      bool operator==( RHS const & ) const {
        return false;
      }

    }; // select_expression

    struct store_expression {
      logic_expression array;
      logic_expression index;
      logic_expression value;

      store_expression( logic_expression const &array,
                        logic_expression const &index,
                        logic_expression const &value )
        : array( array )
        , index( index )
        , value( value )
      {}

      bool operator==( store_expression const &rhs ) const {
        return boost::tie(array, index, value) == boost::tie(rhs.array, rhs.index, rhs.value);
      }

      template < typename RHS >
      bool operator==( RHS const & ) const {
        return false;
      }

    }; // store_expression

  } // expression
} // metaSMT
