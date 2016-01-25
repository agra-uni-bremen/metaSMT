#pragma once
#include "expression.hpp"
#include "../support/DefaultSymbolTable.hpp"
#include <boost/spirit/include/karma.hpp>
#include <boost/spirit/include/karma_eps.hpp>
#include <boost/spirit/include/karma_string.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_bind.hpp>
#include <boost/fusion/include/adapt_struct.hpp>
#include <boost/algorithm/string/trim.hpp>

BOOST_FUSION_ADAPT_STRUCT(
  metaSMT::expression::bv_const<metaSMT::logic::QF_BV::tag::bvuint_tag>,
  (unsigned long, value)
  (unsigned long, width)
)

BOOST_FUSION_ADAPT_STRUCT(
  metaSMT::expression::bv_const<metaSMT::logic::QF_BV::tag::bvsint_tag>,
  (unsigned long, value)
  (unsigned long, width)
)

BOOST_FUSION_ADAPT_STRUCT(
  metaSMT::expression::bv_const<metaSMT::logic::QF_BV::tag::bvhex_tag>,
  (std::string, str)
)

BOOST_FUSION_ADAPT_STRUCT(
  metaSMT::expression::bv_const<metaSMT::logic::QF_BV::tag::bvbin_tag>,
  (std::string, str)
)

BOOST_FUSION_ADAPT_TPL_STRUCT(
  (ReturnTag)(OpTag),
  (metaSMT::expression::unary_expression)(ReturnTag)(OpTag),
  (metaSMT::expression::logic_expression,expr)
)

BOOST_FUSION_ADAPT_TPL_STRUCT(
  (ReturnTag)(OpTag),
  (metaSMT::expression::binary_expression)(ReturnTag)(OpTag),
  (metaSMT::expression::logic_expression,left)
  (metaSMT::expression::logic_expression,right)
)

BOOST_FUSION_ADAPT_TPL_STRUCT(
  (ReturnTag)(OpTag),
  (metaSMT::expression::ternary_expression)(ReturnTag)(OpTag),
  (metaSMT::expression::logic_expression,expr1)
  (metaSMT::expression::logic_expression,expr2)
  (metaSMT::expression::logic_expression,expr3)
)

BOOST_FUSION_ADAPT_TPL_STRUCT(
  (ReturnTag)(OpTag),
  (metaSMT::expression::nary_expression)(ReturnTag)(OpTag),
  (std::vector<metaSMT::expression::logic_expression>,exprs)
)

BOOST_FUSION_ADAPT_STRUCT(
  metaSMT::logic::predicate,
)

BOOST_FUSION_ADAPT_STRUCT(
  metaSMT::logic::QF_BV::bitvector,
)

BOOST_FUSION_ADAPT_STRUCT(
  metaSMT::logic::Array::array,
)

BOOST_FUSION_ADAPT_STRUCT(
  metaSMT::logic::QF_UF::Uninterpreted_Function,
)

BOOST_FUSION_ADAPT_TPL_STRUCT(
  (OpTag),
  (metaSMT::expression::extend_expression)(OpTag),
  (unsigned long,by)
  (metaSMT::expression::logic_expression,expr)
)

BOOST_FUSION_ADAPT_TPL_STRUCT(
  (OpTag),
  (metaSMT::expression::extract_expression)(OpTag),
  (unsigned long,from)
  (unsigned long,to)
  (metaSMT::expression::logic_expression,expr)
)

BOOST_FUSION_ADAPT_STRUCT(
  metaSMT::expression::select_expression,
  (metaSMT::expression::logic_expression,array)
  (metaSMT::expression::logic_expression,index)
)

BOOST_FUSION_ADAPT_STRUCT(
  metaSMT::expression::store_expression,
  (metaSMT::expression::logic_expression,array)
  (metaSMT::expression::logic_expression,index)
  (metaSMT::expression::logic_expression,value)
)

namespace metaSMT {
  namespace expression {
    namespace spirit = boost::spirit;
    namespace karma = boost::spirit::karma;

    std::string print_expression( logic_expression const &expr,
                                  boost::function<std::string(unsigned)> const &table = support::default_symbol_table );

    template < typename OutputIterator >
    struct grammar : karma::grammar< OutputIterator, logic_expression() > {
      void predicate_to_string(std::string &s, metaSMT::logic::predicate const &p) {
        predtags::var_tag tag = boost::proto::value(p);
        assert( tag.id != 0 && "predicate id number must not be zero" );

        std::ostringstream os;
        os << table(tag.id);
        s = os.str();
      }

      void bitvector_to_string(std::string &s, metaSMT::logic::QF_BV::bitvector const &bv) {
        bvtags::var_tag tag = boost::proto::value(bv);
        assert( tag.id != 0 && "bit-vector id number must not be zero" );
        assert( tag.width != 0 && "bit-vector width must not be zero" );

        std::stringstream os;
        os << table(tag.id);
        s = os.str();
      }

      void array_to_string(std::string &s, metaSMT::logic::Array::array const &array) {
        arraytags::array_var_tag tag = boost::proto::value(array);
        assert( tag.id != 0 && "array id number must not be zero" );

        std::ostringstream os;
        os << table(tag.id);
        s = os.str();
      }

      void uf_to_string(std::string &s, metaSMT::logic::QF_UF::Uninterpreted_Function const &uf) {
        uftags::function_var_tag tag = boost::proto::value(uf);
        assert( tag.id != 0 && "uninterpreted function id number must not be zero" );

        std::ostringstream os;
        os << table(tag.id);
        s = os.str();
      }

      grammar( boost::function<std::string(unsigned)> const &table )
        : grammar::base_type(main_rule)
        , table(table) {

        main_rule %=
        // constants
          bool_rule
        | bit0_rule
        | bit1_rule
        | bvuint_rule
        | bvsint_rule
        | bvhex_rule
        | bvbin_rule

        // variables
        | predicate_rule
        | bitvector_rule
        | array_rule
        | uf_rule

        // unary_expressions
        | not_rule
        | bvnot_rule
        | bvneg_rule

        // binary_expressions
        | equal_rule
        | nequal_rule
        | distinct_rule
        | implies_rule
        | nand_rule
        | nor_rule
        | xor_rule
        | xnor_rule

        | bvand_rule
        | bvnand_rule
        | bvor_rule
        | bvnor_rule
        | bvxor_rule
        | bvxnor_rule

        | bvadd_rule
        | bvsub_rule
        | bvmul_rule
        | bvudiv_rule
        | bvurem_rule
        | bvsdiv_rule
        | bvsrem_rule

        | bvshl_rule
        | bvshr_rule
        | bvashr_rule

        | bvcomp_rule
        | bvslt_rule
        | bvsle_rule
        | bvsge_rule
        | bvsgt_rule
        | bvult_rule
        | bvule_rule
        | bvuge_rule
        | bvugt_rule

        | concat_rule

        // ternary expressions
        | ite_rule
          
        // nary expressions
        | nary_uf_rule
        | nary_and_rule
        | nary_or_rule

        // expressions with special syntax
        | extract_rule
        | zero_extend_rule
        | sign_extend_rule
        | select_rule
        | store_rule

        | spirit::eps
        ;

        // constants
        bool_rule %= spirit::bool_;
        bit0_rule %= spirit::eps << spirit::lit("#b0");
        bit1_rule %= spirit::eps << spirit::lit("#b1");
        bvuint_rule %= spirit::eps << spirit::lit("(_ bv") << spirit::ulong_ << spirit::lit(' ') << spirit::ulong_ << spirit::lit(')');
        bvsint_rule %= spirit::eps << spirit::lit("(_ bv") << spirit::ulong_ << spirit::lit(' ') << spirit::ulong_ << spirit::lit(')');
        bvbin_rule %= spirit::eps << spirit::lit("#b") << spirit::ascii::string;
        bvhex_rule %= spirit::eps << spirit::lit("#x") << spirit::ascii::string;

        // variables
        predicate_rule = karma::string[boost::phoenix::bind(&grammar<OutputIterator>::predicate_to_string, this, spirit::_1, spirit::_val)];
        bitvector_rule = karma::string[boost::phoenix::bind(&grammar<OutputIterator>::bitvector_to_string, this, spirit::_1, spirit::_val)];
        array_rule = karma::string[boost::phoenix::bind(&grammar<OutputIterator>::array_to_string, this, spirit::_1, spirit::_val)];
        uf_rule = karma::string[boost::phoenix::bind(&grammar<OutputIterator>::uf_to_string, this, spirit::_1, spirit::_val)];

        // unary_expression
        not_rule %= spirit::eps << spirit::lit("(not ") << main_rule << spirit::lit(")");
        bvnot_rule %= spirit::eps << spirit::lit("(bvnot ") << main_rule << spirit::lit(")");
        bvneg_rule %= spirit::eps << spirit::lit("(bvneg ") << main_rule << spirit::lit(")");

        // binary_expressions
        implies_rule %= spirit::eps << spirit::lit("(=> ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        xor_rule %= spirit::eps << spirit::lit("(xor ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        nand_rule %= spirit::eps << spirit::lit("(not (and ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit("))");
        nor_rule %= spirit::eps << spirit::lit("(not (or ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit("))");
        xnor_rule %= spirit::eps << spirit::lit("(not (xor ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit("))");
        equal_rule %= spirit::eps << spirit::lit("(= ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        nequal_rule %= spirit::eps << spirit::lit("(not (= ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit("))");
        distinct_rule %= spirit::eps << spirit::lit("(distinct ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");

        bvand_rule %= spirit::eps << spirit::lit("(bvand ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvor_rule %= spirit::eps << spirit::lit("(bvor ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvxor_rule %= spirit::eps << spirit::lit("(bvxor ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvnand_rule %= spirit::eps << spirit::lit("(bvnand ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvnor_rule %= spirit::eps << spirit::lit("(bvnor ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvxnor_rule %= spirit::eps << spirit::lit("(bvxnor ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");

        bvadd_rule %= spirit::eps << spirit::lit("(bvadd ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvsub_rule %= spirit::eps << spirit::lit("(bvsub ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvmul_rule %= spirit::eps << spirit::lit("(bvmul ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvudiv_rule %= spirit::eps << spirit::lit("(bvudiv ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvurem_rule %= spirit::eps << spirit::lit("(bvurem ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvsdiv_rule %= spirit::eps << spirit::lit("(bvsdiv ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvsrem_rule %= spirit::eps << spirit::lit("(bvsrem ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");

        bvshl_rule %= spirit::eps << spirit::lit("(bvshl ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvshr_rule %= spirit::eps << spirit::lit("(bvlshr ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvashr_rule %= spirit::eps << spirit::lit("(bvashr ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");

        bvcomp_rule %= spirit::eps << spirit::lit("(bvcomp ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvslt_rule %= spirit::eps << spirit::lit("(bvslt ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvsle_rule %= spirit::eps << spirit::lit("(bvsle ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvsge_rule %= spirit::eps << spirit::lit("(bvsge ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvsgt_rule %= spirit::eps << spirit::lit("(bvsgt ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvult_rule %= spirit::eps << spirit::lit("(bvult ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvule_rule %= spirit::eps << spirit::lit("(bvule ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvuge_rule %= spirit::eps << spirit::lit("(bvuge ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        bvugt_rule %= spirit::eps << spirit::lit("(bvugt ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");

        concat_rule %= spirit::eps << spirit::lit("(concat ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");

        // ternary expressions
        ite_rule %= spirit::eps << spirit::lit("(ite ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");

        // nary expressions
        nary_uf_rule %= spirit::eps << spirit::lit("(") << *(main_rule << spirit::lit(" ")) << spirit::lit(")");
        nary_and_rule %= spirit::eps << spirit::lit("(and ") << *(main_rule << spirit::lit(" ")) << spirit::lit(")");
        nary_or_rule %= spirit::eps << spirit::lit("(or ") << *(main_rule << spirit::lit(" ")) << spirit::lit(")");

        // expressions with special syntax
        extract_rule %= spirit::eps << spirit::lit("((_ extract ") << spirit::ulong_ << spirit::lit(" ") << spirit::ulong_ << spirit::lit(")") << spirit::lit(" ") << main_rule << spirit::lit(")");
        zero_extend_rule %= spirit::eps << spirit::lit("((_ zero_extend ") << spirit::uint_ << spirit::lit(") ") << main_rule << spirit::lit(")");
        sign_extend_rule %= spirit::eps << spirit::lit("((_ sign_extend ") << spirit::uint_ << spirit::lit(") ") << main_rule << spirit::lit(")");
        select_rule %= spirit::eps << spirit::lit("(select ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
        store_rule %= spirit::eps << spirit::lit("(store ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(" ") << main_rule << spirit::lit(")");
      }

      boost::function<std::string(unsigned)> const &table;

      // main rule
      karma::rule<OutputIterator, logic_expression()> main_rule;

      // constants
      karma::rule<OutputIterator, bool()> bool_rule;
      karma::rule<OutputIterator, bit0_const()> bit0_rule;
      karma::rule<OutputIterator, bit1_const()> bit1_rule;
      karma::rule<OutputIterator, bv_const<bvtags::bvuint_tag>()> bvuint_rule;
      karma::rule<OutputIterator, bv_const<bvtags::bvsint_tag>()> bvsint_rule;
      karma::rule<OutputIterator, bv_const<bvtags::bvbin_tag>()> bvbin_rule;
      karma::rule<OutputIterator, bv_const<bvtags::bvhex_tag>()> bvhex_rule;

      // variables
      karma::rule<OutputIterator, metaSMT::logic::predicate()> predicate_rule;
      karma::rule<OutputIterator, metaSMT::logic::QF_BV::bitvector()> bitvector_rule;
      karma::rule<OutputIterator, metaSMT::logic::Array::array()> array_rule;
      karma::rule<OutputIterator, metaSMT::logic::QF_UF::Uninterpreted_Function()> uf_rule;

      // unary_expression
      karma::rule<OutputIterator, unary_expression<logic_tag, predtags::not_tag>()> not_rule;
      karma::rule<OutputIterator, unary_expression<bv_tag, bvtags::bvnot_tag>()> bvnot_rule;
      karma::rule<OutputIterator, unary_expression<bv_tag, bvtags::bvneg_tag>()> bvneg_rule;

      // binary expression
      karma::rule<OutputIterator, binary_expression<logic_tag, predtags::implies_tag>()> implies_rule;
      karma::rule<OutputIterator, binary_expression<logic_tag, predtags::xor_tag>()> xor_rule;
      karma::rule<OutputIterator, binary_expression<logic_tag, predtags::nand_tag>()> nand_rule;
      karma::rule<OutputIterator, binary_expression<logic_tag, predtags::nor_tag>()> nor_rule;
      karma::rule<OutputIterator, binary_expression<logic_tag, predtags::xnor_tag>()> xnor_rule;

      karma::rule<OutputIterator, binary_expression<logic_tag, predtags::equal_tag>()> equal_rule;
      karma::rule<OutputIterator, binary_expression<logic_tag, predtags::nequal_tag>()> nequal_rule;
      karma::rule<OutputIterator, binary_expression<logic_tag, predtags::distinct_tag>()> distinct_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvand_tag>()> bvand_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvor_tag>()> bvor_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvxor_tag>()> bvxor_rule;

      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvnand_tag>()> bvnand_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvnor_tag>()> bvnor_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvxnor_tag>()> bvxnor_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvadd_tag>()> bvadd_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvsub_tag>()> bvsub_rule;

      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvmul_tag>()> bvmul_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvudiv_tag>()> bvudiv_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvurem_tag>()> bvurem_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvsdiv_tag>()> bvsdiv_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvsrem_tag>()> bvsrem_rule;

      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvshl_tag>()> bvshl_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvshr_tag>()> bvshr_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvashr_tag>()> bvashr_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::bvcomp_tag>()> bvcomp_rule;
      karma::rule<OutputIterator, binary_expression<logic_tag, bvtags::bvslt_tag>()> bvslt_rule;

      karma::rule<OutputIterator, binary_expression<logic_tag, bvtags::bvsle_tag>()> bvsle_rule;
      karma::rule<OutputIterator, binary_expression<logic_tag, bvtags::bvsge_tag>()> bvsge_rule;
      karma::rule<OutputIterator, binary_expression<logic_tag, bvtags::bvsgt_tag>()> bvsgt_rule;
      karma::rule<OutputIterator, binary_expression<logic_tag, bvtags::bvult_tag>()> bvult_rule;
      karma::rule<OutputIterator, binary_expression<logic_tag, bvtags::bvule_tag>()> bvule_rule;

      karma::rule<OutputIterator, binary_expression<logic_tag, bvtags::bvuge_tag>()> bvuge_rule;
      karma::rule<OutputIterator, binary_expression<logic_tag, bvtags::bvugt_tag>()> bvugt_rule;
      karma::rule<OutputIterator, binary_expression<bv_tag, bvtags::concat_tag>()> concat_rule;

      // ternary expressions
      karma::rule<OutputIterator, ternary_expression<logic_tag, predtags::ite_tag>()> ite_rule;

      // nary expression
      karma::rule<OutputIterator, nary_expression<uf_tag, proto::tag::function>()> nary_uf_rule;
      karma::rule<OutputIterator, nary_expression<logic_tag, predtags::and_tag>()> nary_and_rule;
      karma::rule<OutputIterator, nary_expression<logic_tag, predtags::or_tag>()> nary_or_rule;

      // expressions with special syntax
      karma::rule<OutputIterator, extract_expression<bvtags::extract_tag>()> extract_rule;
      karma::rule<OutputIterator, extend_expression<bvtags::zero_extend_tag>()> zero_extend_rule;
      karma::rule<OutputIterator, extend_expression<bvtags::sign_extend_tag>()> sign_extend_rule;
      karma::rule<OutputIterator, select_expression()> select_rule;
      karma::rule<OutputIterator, store_expression()> store_rule;
    }; // grammar

    template < typename OutputIterator >
    bool print_expression( OutputIterator &out_it,
                           logic_expression const &expr,
                           boost::function<std::string(unsigned)> const &table ) {
      grammar<OutputIterator> g(table);
      return karma::generate_delimited(out_it, g, spirit::ascii::space, expr);
    }

  } // expression
} // metaSMT
