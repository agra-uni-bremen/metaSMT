#pragma once
#include "../support/DefaultSymbolTable.hpp"
#include "expression.hpp"
#include <boost/variant/static_visitor.hpp>
#include <boost/format.hpp>

namespace metaSMT {
  namespace expression {
    // forward declarations
    void collect_decls( std::set< std::string > &decls, logic_expression const &expr,
                        boost::function<std::string(unsigned)> const &table = support::default_symbol_table );

    struct type_visitor : boost::static_visitor<std::string> {
      type_visitor() {}

      std::string operator() (type::Array const &arg) const {
        return boost::str( boost::format("(Array (_ BitVec %u) (_ BitVec %u))")
                           % arg.index_width % arg.elem_width );
      }

      std::string operator() (type::BitVector const &arg) const {
        return boost::str( boost::format("(_ BitVec %u)") % arg.width );
      }

      std::string operator() (type::Boolean const &arg) const {
        return "Bool";
      }

    }; // type_visitor

    /**
     * @brief Recursively visits a logic_expression and collects the
     * declarations of all variables in a set of std::strings.
     *
     * \tparam decls Set of declarations
     * \tparam table Symbol table
     **/
    struct collect_declaration_visitor : public boost::static_visitor<> {
      collect_declaration_visitor(std::set< std::string > &decls,
                                  boost::function<std::string(unsigned)> const &table = support::default_symbol_table)
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

    inline void collect_decls( std::set< std::string > &decls,
                               logic_expression const &expr,
                               boost::function<std::string(unsigned)> const &table ) {
      boost::apply_visitor( collect_declaration_visitor(decls, table), expr );
    }
  } // expression
} // metaSMT
