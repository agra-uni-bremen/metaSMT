#pragma once
#include <algorithm>

#include <boost/variant/static_visitor.hpp>
#include <boost/format.hpp>

#include "expression.hpp"
#include "visitors.hpp"

namespace metaSMT {
  namespace expression {
    logic_expression simplify( logic_expression e );

    struct simplify_visitor : public boost::static_visitor< logic_expression > {
      simplify_visitor() {}

      logic_expression operator() ( bool b ) const {
        return b;
      }

      logic_expression operator() ( logic::predicate p ) const {
        return p;
      }

      logic_expression operator() ( unary_expression<logic_tag, predtags::not_tag> expr ) const {
        logic_expression arg = simplify(expr.expr);

        if ( has_type<bool>( arg ) ) {
          bool b = boost::get<bool>( arg );
          return !b;
        }

        if ( has_type< unary_expression<logic_tag, predtags::not_tag> >(arg) ) {
          unary_expression<logic_tag, predtags::not_tag> not_arg = boost::get<unary_expression<logic_tag, predtags::not_tag> >(arg);
          return simplify(not_arg.expr);
        }

        return unary_expression<logic_tag, predtags::not_tag>(arg);
      }

      logic_expression operator() ( binary_expression<logic_tag, predtags::equal_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // ( expr e == expr e ) ==> true
        if ( lhs == rhs ) {
          return true;
        }

        return binary_expression<logic_tag, predtags::equal_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, predtags::nequal_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // ( expr e != expr e ) ==> false
        if ( lhs == rhs ) {
          return false;
        }

        return binary_expression<logic_tag, predtags::nequal_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, predtags::implies_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // true  -> predicate p ==> predicate p
        // false -> predicate p ==> true
        if ( has_type<bool>( lhs ) ) {
          bool b = boost::get<bool>(lhs);
          if ( b ) {
            return rhs;
          } else {
            return true;
          }
        }

        // predicate p --> true  ==> true
        // predicate p --> false ==> !(predicate p)
        if ( has_type< bool >( rhs ) ) {
          bool b = boost::get<bool>( rhs );
          if ( b ) {
            return true;
          } else {
            return unary_expression<logic_tag, predtags::not_tag>(lhs);
          }
        }

        // ( expr e -> expr e ) ==> true
        if ( lhs == rhs ) {
          return true;
        }

        return binary_expression<logic_tag, predtags::implies_tag>(lhs, rhs);
      }

      logic_expression operator() ( nary_expression<logic_tag, predtags::and_tag> expr ) const {
        typedef nary_expression<logic_tag, predtags::and_tag> nary_and;
        nary_and::ContainerType v;
        for (nary_and::ContainerType::const_iterator it = expr.begin(), ie = expr.end();
             it != ie; ++it) {
          logic_expression e = simplify( *it );
          if ( has_type< bool >( e ) ) {
            bool b = boost::get<bool>( e );
            if ( b ) {
              // skip trues
              continue;
            } else {
              // simplify to false
              return false;
            }
          }

          // merge with child
          if ( has_type<nary_and>(e) ) {
            nary_and child = boost::get<nary_and>(e);
            v.insert( v.end(), child.begin(), child.end() );
            continue;
          }

          v.push_back( e );
        }

        unsigned const size = v.size();
        if (size == 0) {
          return true;
        }
        else if (size == 1) {
          return v[0];
        }

        return nary_and(v);
      }

      logic_expression operator() ( nary_expression<logic_tag, predtags::or_tag> expr ) const {
        typedef nary_expression<logic_tag, predtags::or_tag> nary_or;
        nary_or::ContainerType v;
        for (nary_or::ContainerType::const_iterator it = expr.begin(), ie = expr.end();
             it != ie; ++it) {
          logic_expression e = simplify( *it );
          if ( has_type< bool >( e ) ) {
            bool b = boost::get<bool>( e );
            if ( b ) {
              // simplify to true
              return true;
            } else {
              // skip falses
              continue;
            }
          }

          // merge with child
          if ( has_type<nary_or>(e) ) {
            nary_or child = boost::get<nary_or>(e);
            v.insert( v.end(), child.begin(), child.end() );
            continue;
          }

          v.push_back( e );
        }

        unsigned const size = v.size();
        if (size == 0) {
          return false;
        }
        else if (size == 1) {
          return v[0];
        }

        return nary_or(v);
      }

      logic_expression operator() ( binary_expression<logic_tag, predtags::nand_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // !( true  /\ expr ) ==> !(expr)
        // !( false /\ expr ) ==> true
        if ( has_type< bool >( lhs ) ) {
          bool b = boost::get<bool>( lhs );
          if ( b ) {
            return simplify( unary_expression<logic_tag, predtags::not_tag>(rhs) );
          } else {
            return true;
          }
        }

        // !( expr /\ true  ) ==> !(expr)
        // !( expr /\ false ) ==> true
        if ( has_type< bool >( rhs ) ) {
          bool b = boost::get<bool>( rhs );
          if ( b ) {
            return simplify( unary_expression<logic_tag, predtags::not_tag>(lhs) );
          } else {
            return true;
          }
        }

        // !( expr e /\ expr e ) ==> !( expr e )
        if ( lhs == rhs ) {
          return simplify( unary_expression<logic_tag, predtags::not_tag>(lhs) );
        }

        return binary_expression<logic_tag, predtags::nand_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, predtags::nor_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // !( true  \/ expr ) ==> false
        // !( false \/ expr ) ==> !(expr)
        if ( has_type< bool >( lhs ) ) {
          bool b = boost::get<bool>( lhs );
          if ( b ) {
            return false;
          } else {
            return simplify( unary_expression<logic_tag, predtags::not_tag>(rhs) );
          }
        }

        // !( expr \/ true  ) ==> false
        // !( expr \/ false ) ==> !(expr)
        if ( has_type< bool >( rhs ) ) {
          bool b = boost::get<bool>( rhs );
          if ( b ) {
            return true;
          } else {
            return simplify( unary_expression<logic_tag, predtags::not_tag>(lhs) );
          }
        }

        // !( predicate p \/ predicate p ) ==> !( predicate p )
        if ( lhs == rhs ) {
          return simplify( unary_expression<logic_tag, predtags::not_tag>(lhs) );
        }

        return binary_expression<logic_tag, predtags::nor_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, predtags::xor_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // ( true  xor expr ) ==> !(expr)
        // ( false xor expr ) ==> expr
        if ( has_type< bool >( lhs ) ) {
          bool b = boost::get<bool>( lhs );
          if ( b ) {
            return simplify( unary_expression<logic_tag, predtags::not_tag>(rhs) );
          } else {
            return rhs;
          }
        }

        // ( expr xor true  ) ==> !(expr)
        // ( expr xor false ) ==> expr
        if ( has_type< bool >( rhs ) ) {
          bool b = boost::get<bool>( rhs );
          if ( b ) {
            return simplify( unary_expression<logic_tag, predtags::not_tag>(lhs) );
          } else {
            return lhs;
          }
        }

        // ( expr e xor expr e ) ==> false
        if ( lhs == rhs ) {
          return false;
        }

        return binary_expression<logic_tag, predtags::xor_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, predtags::xnor_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // !( true  xor expr ) ==> expr
        // !( false xor expr ) ==> !(expr)
        if ( has_type< bool >( lhs ) ) {
          bool b = boost::get<bool>( lhs );
          if ( b ) {
            return rhs;
          } else {
            return simplify( unary_expression<logic_tag, predtags::not_tag>(rhs) );
          }
        }

        // !( expr xor true  ) ==> expr
        // !( expr xor false ) ==> !(expr)
        if ( has_type< bool >( rhs ) ) {
          bool b = boost::get<bool>( rhs );
          if ( b ) {
            return lhs;
          } else {
            return simplify( unary_expression<logic_tag, predtags::not_tag>(lhs) );
          }
        }

        // !( expr e xor expr e ) ==> true
        if ( lhs == rhs ) {
          return true;
        }

        return binary_expression<logic_tag, predtags::xnor_tag>(lhs, rhs);
      }

      logic_expression operator() ( ternary_expression<logic_tag, predtags::ite_tag> expr ) const {
        logic_expression cond = simplify(expr.expr1);
        logic_expression true_expr = simplify(expr.expr2);
        logic_expression false_expr = simplify(expr.expr3);

        // ite( true,  t_expr, f_expr) ==> t_expr
        // ite( false, t_expr, f_expr) ==> f_expr
        if ( has_type< bool >( cond ) ) {
          bool b = boost::get<bool>( cond );
          if ( b ) {
            return true_expr;
          } else {
            return false_expr;
          }
        }

        // ite( cond, expr, expr ) ==> expr
        if ( true_expr == false_expr ) {
          return true_expr;
        }

        return ternary_expression<logic_tag, predtags::ite_tag>(cond, true_expr, false_expr);
      }

      logic_expression operator() ( bit0_const b ) const {
        return b;
      }

      logic_expression operator() ( bit1_const b ) const {
        return b;
      }

      template < typename OpTag >
      logic_expression operator() ( bv_const<OpTag> const &expr ) const {
        if (expr.width == 1) {
          if (expr.value == 0) {
            return logic::QF_BV::bit0;
          }
          else {
            return logic::QF_BV::bit1;
          }
        }
        return expr;
      }

      logic_expression operator() ( logic::QF_BV::bitvector bv ) const {
        return bv;
      }

      logic_expression operator() ( unary_expression<bv_tag, bvtags::bvnot_tag> expr ) const {
        logic_expression arg = simplify(expr.expr);
        // not( bit0 ) ==> bit1
        if ( has_type< bit0_const >( arg ) ) {
          return logic::QF_BV::bit1;
        }
        // not( bit1 ) ==> bit0
        else if ( has_type< bit1_const >( arg ) ) {
          return logic::QF_BV::bit0;
        }
        else if ( has_type< unary_expression<bv_tag, bvtags::bvnot_tag> >(arg) ) {
          unary_expression<bv_tag, bvtags::bvnot_tag> not_arg = boost::get<unary_expression<bv_tag, bvtags::bvnot_tag> >(arg);
          return simplify(not_arg.expr);
        }

        return unary_expression<bv_tag, bvtags::bvnot_tag>(arg);
      }

      logic_expression operator() ( unary_expression<bv_tag, bvtags::bvneg_tag> expr ) const {
        return expr;
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvand_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // ( expr e /\ expr e ) ==> expr e
        if ( lhs == rhs ) {
          return lhs;
        }

        if ( has_type< binary_expression<bv_tag, bvtags::bvand_tag> >(lhs) ) {
          // TODO
        }

        if ( has_type< binary_expression<bv_tag, bvtags::bvand_tag> >(rhs) ) {
          // TODO
        }

        return binary_expression<bv_tag, bvtags::bvand_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvnand_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // !( expr e /\ expr e ) ==> !(expr e)
        if ( lhs == rhs ) {
          return unary_expression<bv_tag, bvtags::bvnot_tag>(lhs);
        }

        return binary_expression<bv_tag, bvtags::bvnand_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvor_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // ( expr e \/ expr e ) ==> expr e
        if ( lhs == rhs ) {
          return lhs;
        }

        return binary_expression<bv_tag, bvtags::bvor_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvnor_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // !( expr e \/ expr e ) ==> !( expr e )
        if ( lhs == rhs ) {
          return unary_expression<bv_tag, bvtags::bvnot_tag>(lhs);
        }

        return binary_expression<bv_tag, bvtags::bvnor_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvxor_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<bv_tag, bvtags::bvxor_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvxnor_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<bv_tag, bvtags::bvxnor_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvshl_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // expr e << 0 ==> expr e
        if ( has_type< bit0_const >(rhs) ) {
          return lhs;
        }

        return binary_expression<bv_tag, bvtags::bvshl_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvshr_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // expr e >> 0 ==> expr e
        if ( has_type< bit0_const >(rhs) ) {
          return lhs;
        }

        return binary_expression<bv_tag, bvtags::bvshr_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvashr_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // expr e >> 0 ==> expr e
        if ( has_type< bit0_const >(rhs) ) {
          return lhs;
        }

        return binary_expression<bv_tag, bvtags::bvashr_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvadd_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // expr e + 0 ==> expr e
        if ( has_const_value(rhs, 0) ) {
          return lhs;
        }

        // 0 + expr e ==> expr e
        if ( has_const_value(lhs, 0) ) {
          return rhs;
        }

        return binary_expression<bv_tag, bvtags::bvadd_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvsub_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // expr e - 0 ==> expr e
        if ( has_const_value(rhs, 0) ) {
          return lhs;
        }

        // 0 - expr e ==> expr -e
        if ( has_const_value(lhs, 0) ) {
          return unary_expression<bv_tag, bvtags::bvneg_tag>(rhs);
        }

        return binary_expression<bv_tag, bvtags::bvsub_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvmul_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        // TODO: expr e * 0 ==> 0
        // TODO: 0 * expr e ==> 0

        return binary_expression<bv_tag, bvtags::bvmul_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvsrem_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<bv_tag, bvtags::bvsrem_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvsdiv_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<bv_tag, bvtags::bvsdiv_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvurem_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<bv_tag, bvtags::bvurem_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvudiv_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<bv_tag, bvtags::bvudiv_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::bvcomp_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<bv_tag, bvtags::bvcomp_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, bvtags::bvslt_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<logic_tag, bvtags::bvslt_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, bvtags::bvsgt_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<logic_tag, bvtags::bvsgt_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, bvtags::bvsle_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<logic_tag, bvtags::bvsle_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, bvtags::bvsge_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<logic_tag, bvtags::bvsge_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, bvtags::bvult_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<logic_tag, bvtags::bvult_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, bvtags::bvugt_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<logic_tag, bvtags::bvugt_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, bvtags::bvule_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<logic_tag, bvtags::bvule_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<logic_tag, bvtags::bvuge_tag> expr ) const {
        logic_expression lhs = simplify(expr.left);
        logic_expression rhs = simplify(expr.right);

        return binary_expression<logic_tag, bvtags::bvuge_tag>(lhs, rhs);
      }

      logic_expression operator() ( binary_expression<bv_tag, bvtags::concat_tag> expr ) const {
        return expr;
      }

      template < typename T >
      logic_expression operator() ( extract_expression<T> expr ) const {
        return expr;
      }

      template < typename T >
      logic_expression operator() ( extend_expression<T> expr ) const {
        return expr;
      }

      // Fallback
      template < typename T >
      logic_expression operator() ( T const & ) const {
        assert(false);
        return false;
      }

      boost::function<std::string(unsigned)> table_;
    }; // simplify_visitor

    logic_expression simplify( logic_expression e ) {
      return boost::apply_visitor( simplify_visitor(), e );
    }
  } // expression
} // metaSMT
