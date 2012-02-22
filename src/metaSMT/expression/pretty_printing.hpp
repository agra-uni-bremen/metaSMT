#pragma once
#include <boost/variant/static_visitor.hpp>
#include <boost/format.hpp>

#include "expression.hpp"

namespace metaSMT {
  inline std::string default_symbol_table(unsigned id) {
    char buf[64];
    sprintf(buf, "var_%u", id);
    return buf;
  }

  namespace expression {
    // forward declarations
    std::string to_string( logic_expression const &expr,
                           boost::function<std::string(unsigned)> const &table = default_symbol_table );

    void collect_decls( std::set< std::string > &decls, logic_expression const &expr,
                        boost::function<std::string(unsigned)> const &table = default_symbol_table );

    struct type_visitor : boost::static_visitor<std::string> {
      type_visitor() {}

      std::string operator() (type::BitVector const &arg) const {
        return boost::str( boost::format("(_ BitVec %u)") % arg.width );
      }

      std::string operator() (type::Boolean const &arg) const {
        return "Bool";
      }
    }; // type_visitor

    /**
     * @brief Recursively visits a logic_expression and converts it into a std::string.
     *
     * \tparam table Symbol table
     **/
    struct to_string_visitor : public boost::static_visitor<std::string> {
      to_string_visitor( boost::function<std::string(unsigned)> const &table = default_symbol_table )
        : table_(table)
      {}

      std::string operator() ( logic::predicate p ) const {
        predtags::var_tag tag = boost::proto::value(p);
        assert( tag.id != 0 && "predicate id number must not be zero" );
        return table_(tag.id);
      }

      std::string operator() ( bool value ) const {
        return (value ? "true" : "false");
      }

      // unary ops
      typedef boost::mpl::vector<
        predtags::not_tag
      , bvtags::bvnot_tag
      , bvtags::bvneg_tag
      > UnaryOpMap;

      template < typename LogicTag, typename OpTag >
      typename boost::enable_if<
        typename boost::mpl::not_<
        boost::is_same<
          typename boost::mpl::find<UnaryOpMap, OpTag>::type
        , boost::mpl::end<UnaryOpMap>::type
        > >
        , std::string
      >
      ::type operator() ( unary_expression<LogicTag, OpTag> const &op ) const {
        return boost::str( boost::format("(%s %s)") % op.name() % to_string(op.expr, table_) );
      }

      // binary ops
      typedef boost::mpl::vector33<
        predtags::implies_tag
      , predtags::xor_tag
      , predtags::nand_tag
      , predtags::nor_tag
      , predtags::xnor_tag
      , predtags::equal_tag
      , predtags::nequal_tag
      , bvtags::bvand_tag
      , bvtags::bvor_tag
      , bvtags::bvxor_tag
      , bvtags::bvnand_tag
      , bvtags::bvnor_tag
      , bvtags::bvxnor_tag
      , bvtags::bvadd_tag
      , bvtags::bvsub_tag
      , bvtags::bvmul_tag
      , bvtags::bvudiv_tag
      , bvtags::bvurem_tag
      , bvtags::bvsdiv_tag
      , bvtags::bvsrem_tag
      , bvtags::bvshl_tag
      , bvtags::bvshr_tag
      , bvtags::bvashr_tag
      , bvtags::bvcomp_tag
      , bvtags::bvslt_tag
      , bvtags::bvsle_tag
      , bvtags::bvsge_tag
      , bvtags::bvsgt_tag
      , bvtags::bvult_tag
      , bvtags::bvule_tag
      , bvtags::bvuge_tag
      , bvtags::bvugt_tag
      , bvtags::concat_tag
      > BinaryOpMap;

      template < typename LogicTag, typename OpTag >
      typename boost::enable_if<
        typename boost::mpl::not_<
        boost::is_same<
          typename boost::mpl::find<BinaryOpMap, OpTag>::type
        , boost::mpl::end<BinaryOpMap>::type
        > >
        , std::string
      >
      ::type operator() ( binary_expression<LogicTag, OpTag> const &op ) const {
        return boost::str( boost::format("(%s %s %s)") % op.name() % to_string(op.left, table_) % to_string(op.right, table_) );
      }

      std::string operator() ( binary_expression<logic_tag, predtags::nequal_tag> const &op ) const {
        return boost::str( boost::format("(not (= %s %s))") % to_string(op.left, table_) % to_string(op.right, table_) );
      }

      std::string operator() ( binary_expression<logic_tag, predtags::nand_tag> const &op ) const {
        return boost::str( boost::format("(not (and %s %s))") % to_string(op.left, table_) % to_string(op.right, table_) );
      }

      std::string operator() ( binary_expression<logic_tag, predtags::nor_tag> const &op ) const {
        return boost::str( boost::format("(not (or %s %s))") % to_string(op.left, table_) % to_string(op.right, table_) );
      }

      std::string operator() ( binary_expression<logic_tag, predtags::xnor_tag> const &op ) const {
        return boost::str( boost::format("(not (xor %s %s))") % to_string(op.left, table_) % to_string(op.right, table_) );
      }

      // ternary ops
      typedef boost::mpl::vector<
        predtags::ite_tag
      > TernaryOpMap;

      template < typename LogicTag, typename OpTag >
      typename boost::enable_if<
        typename boost::mpl::not_<
        boost::is_same<
        typename boost::mpl::find<TernaryOpMap, OpTag>::type
        , boost::mpl::end<TernaryOpMap>::type
        > >
        , std::string
      >
      ::type operator() ( ternary_expression<LogicTag, OpTag> const &op ) const {
        return boost::str( boost::format("(%s %s %s %s)") % op.name() % to_string(op.expr1, table_) % to_string(op.expr2, table_) % to_string(op.expr3, table_) );
      }

      // nary ops
      typedef boost::mpl::vector<
        predtags::and_tag
      , predtags::or_tag
      > NaryOpMap;

      template < typename LogicTag, typename OpTag >
      typename boost::enable_if<
        typename boost::mpl::not_<
        boost::is_same<
        typename boost::mpl::find<NaryOpMap, OpTag>::type
        , boost::mpl::end<NaryOpMap>::type
        > >
        , std::string
      >
      ::type operator() ( nary_expression<LogicTag, OpTag> const &op ) const {
        typedef typename nary_expression<LogicTag, OpTag>::ContainerType ContainerTy;
        std::string s = "(" + op.name();
        for ( typename ContainerTy::const_iterator it = op.begin(), ie = op.end();
            it != ie; ++it) {
          s += ' ';
          s += to_string(*it, table_);
        }
        s += ')';
        return s;
      }

      // other ops
      std::string operator() ( logic::QF_BV::QF_BV<boost::proto::terminal<metaSMT::logic::QF_BV::tag::bit0_tag>::type > const & ) const {
        return "#b0";
      }

      std::string operator() ( logic::QF_BV::QF_BV<boost::proto::terminal<metaSMT::logic::QF_BV::tag::bit1_tag>::type > const & ) const {
        return "#b1";
      }

      std::string operator() ( logic::QF_BV::bitvector bv ) const {
        bvtags::var_tag tag = boost::proto::value(bv);
        assert( tag.id != 0 && "bit-vector id number must not be zero" );
        assert( tag.width != 0 && "bit-vector width must not be zero" );
        return table_(tag.id);
      }

      std::string operator() ( bv_const<bvtags::bvuint_tag> const &expr ) const {
        return boost::str( boost::format("(_ bv%u %u)")
                           % expr.value % expr.width);
      }

      std::string operator() ( bv_const<bvtags::bvsint_tag> const &expr ) const {
        return boost::str( boost::format("(_ bv%u %u)")
                           % expr.value % expr.width);
      }

      std::string operator() ( bv_const<bvtags::bvbin_tag> const &expr ) const {
        return boost::str( boost::format("#b%s") % expr.str );
      }

      std::string operator() ( bv_const<bvtags::bvhex_tag> const &expr ) const {
        return boost::str( boost::format("#x%s") % expr.str );
      }

      std::string operator() ( extract_expression<bvtags::extract_tag> const &op ) const {
        return boost::str( boost::format("((_ extract %u %u) %s)") % op.from % (op.from - op.width) % to_string(op.expr, table_) );
      }

      std::string operator() ( extend_expression<bvtags::zero_extend_tag> const &op ) const {
        return boost::str( boost::format("((_ zero_extend %u) %s)") % op.by % to_string(op.expr, table_) );
      }

      std::string operator() ( extend_expression<bvtags::sign_extend_tag> const &op ) const {
        return boost::str( boost::format("((_ sign_extend %u) %s)") % op.by % to_string(op.expr, table_) );
      }

      std::string operator() ( logic::Array::array array ) const {
        arraytags::array_var_tag tag = boost::proto::value(array);
        assert( tag.id != 0 && "array id number must not be zero" );
        return table_(tag.id);
      }

      std::string operator() ( select_expression const &select ) const {
        return boost::str( boost::format("(select %s %s)") % to_string(select.array, table_) % to_string(select.index, table_) );
      }

      std::string operator() ( store_expression const &store ) const {
        return boost::str( boost::format("(store %s %s %s)") % to_string(store.array, table_) % to_string(store.index, table_) % to_string(store.value, table_) );
      }

      std::string operator() ( metaSMT::logic::QF_UF::Uninterpreted_Function uf ) const {
        uftags::function_var_tag tag = boost::proto::value(uf);
        assert( tag.id != 0 && "uninterpreted function id number must not be zero" );
        return table_(tag.id);
      }

      std::string operator() ( nary_expression<uf_tag, proto::tag::function> op ) const {
        typedef nary_expression<uf_tag, proto::tag::function>::ContainerType ContainerTy;
        std::string s = "(";
        for ( ContainerTy::const_iterator it = op.begin(), ie = op.end();
              it != ie; ++it ) {
          s += to_string(*it, table_);
          s += ' ';
        }
        s += ')';
        return s;
      }

      // Fallback
      template < typename T >
      std::string operator() ( T const & ) const {
        assert( false && "Yet not implemented." );
        return "";
      }

      boost::function<std::string(unsigned)> table_;
    }; // to_string_visitor

    /**
     * @brief Recursively visits a logic_expression and collects the
     * declarations of all variables in a set of std::strings.
     *
     * \tparam decls Set of declarations
     * \tparam table Symbol table
     **/
    struct collect_declaration_visitor : public boost::static_visitor<> {
      collect_declaration_visitor(std::set< std::string > &decls,
                                  boost::function<std::string(unsigned)> const &table = default_symbol_table)
        : decls_(decls)
        , table_(table)
      {}

      void declare( std::string const &decl ) const {
        decls_.insert(decl);
      }

      void operator() ( logic::predicate p ) const {
        predtags::var_tag tag = boost::proto::value(p);
        assert( tag.id != 0 && "predicate id number must not be zero" );
        declare( boost::str(boost::format("(declare-fun %s () Bool)\n")
                            % table_(tag.id)) );
      }

      void operator() ( logic::QF_BV::bitvector bv ) const {
        bvtags::var_tag tag = boost::proto::value(bv);
        assert( tag.id != 0 && "bit-vector id number must not be zero" );
        assert( tag.width != 0 && "bit-vector width must not be zero" );
        declare( boost::str(boost::format("(declare-fun %s () (_ BitVec %d))\n")
                            % table_(tag.id) % tag.width ) );
      }

      void operator() ( logic::Array::array array ) const {
        arraytags::array_var_tag tag = boost::proto::value(array);
        assert( tag.id != 0 && "array id number must not be zero" );
        declare( boost::str(boost::format("(declare-fun %s () (Array (_ BitVec %d) (_ BitVec %d)))\n")
                            % table_(tag.id) % tag.index_width % tag.elem_width ));
      }

      void operator() ( logic::QF_UF::Uninterpreted_Function uf ) const {
        uftags::function_var_tag tag = boost::proto::value(uf);
        assert( tag.id != 0 && "uninterpreted function id number must not be zero" );
        std::string s = boost::str( boost::format("(declare-fun %s (") % table_(tag.id) );
        unsigned const num_args = tag.args.size();
        for ( unsigned u = 0; u < num_args; ++u ) {
          s += boost::apply_visitor(type_visitor(), tag.args[u]);
          s += ' ';
        }
        s += boost::str( boost::format(") %s)") % boost::apply_visitor(type_visitor(), tag.result_type) );
        declare( s );
      }

      template < typename LogicTag, typename OpTag >
      void operator() ( unary_expression<LogicTag, OpTag> op ) const {
        collect_decls(decls_, op.expr, table_);
      }

      template < typename LogicTag, typename OpTag >
      void operator() ( binary_expression<LogicTag, OpTag> op ) const {
        collect_decls(decls_, op.left, table_);
        collect_decls(decls_, op.right, table_);
      }

      template < typename LogicTag, typename OpTag >
      void operator() ( ternary_expression<LogicTag, OpTag> op ) const {
        collect_decls(decls_, op.expr1, table_);
        collect_decls(decls_, op.expr2, table_);
        collect_decls(decls_, op.expr3, table_);
      }

      template < typename LogicTag, typename OpTag >
      void operator() ( nary_expression<LogicTag, OpTag> op ) const {
        typedef typename nary_expression<LogicTag, OpTag>::ContainerType Ty;
        for (typename Ty::const_iterator it = op.exprs.begin(), ie = op.exprs.end();
             it != ie; ++it) {
          collect_decls(decls_, *it, table_);
        }
      }

      template < typename OpTag >
      void operator() ( extract_expression<OpTag> op ) const {
        collect_decls(decls_, op.expr, table_);
      }

      template < typename OpTag >
      void operator() ( extend_expression<OpTag> op ) const {
        collect_decls(decls_, op.expr, table_);
      }

      void operator() ( select_expression op ) const {
        collect_decls(decls_, op.array, table_);
        collect_decls(decls_, op.index, table_);
      }

      void operator() ( store_expression op ) const {
        collect_decls(decls_, op.array, table_);
        collect_decls(decls_, op.index, table_);
        collect_decls(decls_, op.value, table_);
      }

      // Fallback
      template < typename T >
      void operator() ( T const & ) const {}

      std::set< std::string > &decls_;
      boost::function<std::string(unsigned)> table_;
    }; // collect_declaration_visitor

    inline std::string to_string( logic_expression const &expr,
                                  boost::function<std::string(unsigned)> const &table ) {
      return boost::apply_visitor( to_string_visitor(table), expr );
    }

    inline void collect_decls( std::set< std::string > &decls,
                               logic_expression const &expr,
                               boost::function<std::string(unsigned)> const &table ) {
      boost::apply_visitor( collect_declaration_visitor(decls, table), expr );
    }

  } // expression
} // metaSMT
