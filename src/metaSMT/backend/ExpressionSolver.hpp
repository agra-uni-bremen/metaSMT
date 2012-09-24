#pragma once

#include "../tags/QF_BV.hpp"
#include "../tags/QF_UF.hpp"
#include "../tags/Array.hpp"
#include "../result_wrapper.hpp"

#include <metaSMT/expression/expression.hpp>
#include <metaSMT/expression/pretty_printing.hpp>

namespace metaSMT {
  namespace solver {
    namespace predtags = ::metaSMT::logic::tag;
    namespace bvtags = ::metaSMT::logic::QF_BV::tag;
    namespace arraytags = ::metaSMT::logic::Array::tag;
    namespace uftags = ::metaSMT::logic::QF_UF::tag;
    namespace expr = ::metaSMT::expression;

    template < typename Solver >
    typename Solver::result_type
    make_backend_result_type( Solver &solver, std::map<unsigned, typename Solver::result_type> &var_map, expr::logic_expression const &expr );

    template < typename Solver >
    class result_type_visitor : public boost::static_visitor< typename Solver::result_type > {
    public:
      typedef typename Solver::result_type result_type;
      typedef std::map< unsigned, result_type > VarMap;

      result_type_visitor( Solver &solver,
                           VarMap &var_map )
        : solver(solver)
        , var_map(var_map)
      {}

      // constants
      result_type operator() ( bool value ) const {
        if ( value ) {
          return solver(predtags::true_tag(), boost::any());
        }
        else {
          return solver(predtags::false_tag(), boost::any());
        }
      }

      result_type operator() ( expr::bit0_const bit0 ) const {
        return solver(bvtags::bit0_tag(), boost::any());
      }

      result_type operator() ( expr::bit1_const bit1 ) const {
        return solver(bvtags::bit1_tag(), boost::any());
      }

      result_type operator() ( expr::bv_const<bvtags::bvuint_tag> e ) const {
        return solver( bvtags::bvuint_tag(),
          boost::any(boost::make_tuple<unsigned long, unsigned long>(e.value, e.width)) );
      }

      result_type operator() ( expr::bv_const<bvtags::bvsint_tag> e ) const {
        int const value = static_cast<long>( e.value );
        return solver(bvtags::bvsint_tag(),
          boost::any(boost::make_tuple<long, unsigned long>(value, e.width)) );
      }

      result_type operator() ( expr::bv_const<bvtags::bvhex_tag> e ) const {
        return solver(bvtags::bvhex_tag(), boost::any(e.str));
      }

      result_type operator() ( expr::bv_const<bvtags::bvbin_tag> e ) const {
        return solver(bvtags::bvbin_tag(), boost::any(e.str));
      }

      // variables
      result_type operator() ( logic::predicate p ) const {
        unsigned const id = boost::proto::value(p).id;
        typename VarMap::const_iterator it = var_map.find( id );
        if ( it != var_map.end() ) {
          return it->second;
        }
        result_type r = solver(boost::proto::value(p), boost::any());
        var_map.insert( std::make_pair(id, r) );
        return r;
      }

      result_type operator() ( logic::QF_BV::bitvector bv ) const {
        unsigned const id = boost::proto::value(bv).id;
        typename VarMap::const_iterator it = var_map.find( id );
        if ( it != var_map.end() ) {
          return it->second;
        }
        result_type r = solver(boost::proto::value(bv), boost::any());
        var_map.insert( std::make_pair(id, r) );
        return r;
      }

      result_type operator() ( logic::Array::array a ) const {
        unsigned const id = boost::proto::value(a).id;
        typename VarMap::const_iterator it = var_map.find( id );
        if ( it != var_map.end() ) {
          return it->second;
        }
        result_type r = solver(boost::proto::value(a), boost::any());
        var_map.insert( std::make_pair(id, r) );
        return r;
      }

      result_type operator() ( logic::QF_UF::Uninterpreted_Function uf ) const {
        unsigned const id = boost::proto::value(uf).id;
        typename VarMap::const_iterator it = var_map.find( id );
        if ( it != var_map.end() ) {
          return it->second;
        }
        result_type r = solver(boost::proto::value(uf), boost::any());
        var_map.insert( std::make_pair(id, r) );
        return r;
      }

      // unary expressions
      result_type operator() ( expr::unary_expression<expr::logic_tag, predtags::not_tag> e ) const {
        result_type sub = boost::apply_visitor(*this, e.expr);
        return solver(predtags::not_tag(), sub);
      }

      result_type operator() ( expr::unary_expression<expr::bv_tag, bvtags::bvnot_tag> e ) const {
        result_type sub = boost::apply_visitor(*this, e.expr);
        return solver(bvtags::bvnot_tag(), sub);
      }

      result_type operator() ( expr::unary_expression<expr::bv_tag, bvtags::bvneg_tag> e ) const { 
        result_type sub = boost::apply_visitor(*this, e.expr);
        return solver(bvtags::bvneg_tag(), sub);
      }

      // binary expressions
      result_type operator() ( expr::binary_expression<expr::logic_tag, predtags::equal_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(predtags::equal_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, predtags::nequal_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(predtags::nequal_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, predtags::implies_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(predtags::implies_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, predtags::nand_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(predtags::nand_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, predtags::nor_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(predtags::nor_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, predtags::xor_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(predtags::xor_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, predtags::xnor_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(predtags::xnor_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvand_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvand_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvor_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvor_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvnand_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvnand_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvnor_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvnor_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvxor_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvxor_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvxnor_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvxnor_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvadd_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvadd_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvmul_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvmul_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvsub_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvsub_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvsdiv_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvsdiv_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvsrem_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvsrem_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvudiv_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvudiv_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvurem_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvurem_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvshl_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvshl_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvshr_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvshr_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvashr_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvashr_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::bvcomp_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvcomp_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, bvtags::bvslt_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvslt_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, bvtags::bvsgt_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvsgt_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, bvtags::bvsle_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvsle_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, bvtags::bvsge_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvsge_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, bvtags::bvult_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvult_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, bvtags::bvugt_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvugt_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, bvtags::bvule_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvule_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::logic_tag, bvtags::bvuge_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::bvuge_tag(), lhs, rhs);
      }

      result_type operator() ( expr::binary_expression<expr::bv_tag, bvtags::concat_tag> e ) const {
        result_type lhs = boost::apply_visitor(*this, e.left);
        result_type rhs = boost::apply_visitor(*this, e.right);
        return solver(bvtags::concat_tag(), lhs, rhs);
      }

      // ternary expressions
      result_type operator() ( expr::ternary_expression<expr::logic_tag, predtags::ite_tag> e ) const {
        result_type e1 = boost::apply_visitor(*this, e.expr1);
        result_type e2 = boost::apply_visitor(*this, e.expr2);
        result_type e3 = boost::apply_visitor(*this, e.expr3);
        return solver(predtags::ite_tag(), e1, e2, e3);
      }

      // nary expressions
      result_type operator() ( expr::nary_expression<expr::uf_tag, proto::tag::function> e ) const {
        assert( false && "Yet not implemented" );
        return solver(predtags::false_tag(), boost::any());
      }

      result_type operator() ( expr::nary_expression<expr::logic_tag, predtags::and_tag> e ) const {
        typedef expr::nary_expression<expr::logic_tag, predtags::and_tag> Expr;
        result_type r = solver(predtags::true_tag(), boost::any());
        for ( Expr::ContainerType::const_iterator it = e.begin(), ie = e.end(); it != ie; ++it ) {
          result_type arg = boost::apply_visitor(*this, *it);
          r = solver(predtags::and_tag(), r, arg);
        }
        return r;
      }

      result_type operator() ( expr::nary_expression<expr::logic_tag, predtags::or_tag> e ) const {
        typedef expr::nary_expression<expr::logic_tag, predtags::or_tag> Expr;
        result_type r = solver(predtags::false_tag(), boost::any());
        for (  Expr::ContainerType::const_iterator it = e.begin(), ie = e.end(); it != ie; ++it ) {
          result_type arg = boost::apply_visitor(*this, *it);
          r = solver(predtags::or_tag(), r, arg);
        }
        return r;
      }

      // expressions with special syntax
      result_type operator() ( expr::extract_expression<bvtags::extract_tag> e ) const {
        result_type expr = boost::apply_visitor(*this, e.expr);
        return solver(bvtags::extract_tag(), e.from, e.from-e.width, expr);
      }

      result_type operator() ( expr::extend_expression<bvtags::zero_extend_tag> e ) const {
        result_type expr = boost::apply_visitor(*this, e.expr);
        return solver(bvtags::zero_extend_tag(), e.by, expr);
      }

      result_type operator() ( expr::extend_expression<bvtags::sign_extend_tag> e ) const {
        result_type expr = boost::apply_visitor(*this, e.expr);
        return solver(bvtags::sign_extend_tag(), e.by, expr);
      }

      result_type operator() ( expr::select_expression e ) const {
        result_type array = boost::apply_visitor(*this, e.array);
        result_type index = boost::apply_visitor(*this, e.index);
        return solver(arraytags::select_tag(), array, index);
      }

      result_type operator() ( expr::store_expression e ) const {
        result_type array = boost::apply_visitor(*this, e.array);
        result_type index = boost::apply_visitor(*this, e.index);
        result_type value = boost::apply_visitor(*this, e.value);
        return solver(arraytags::store_tag(), array, index, value);
      }

      template < typename TagT >
      result_type operator() ( TagT ) const {
        assert( false );
      }

    private:
      Solver &solver;
      VarMap &var_map;
    };

    template < typename Solver >
    inline typename Solver::result_type
    make_backend_result_type( Solver &solver, std::map<unsigned, typename Solver::result_type> &var_map, expr::logic_expression const &expr ) {
      return boost::apply_visitor( result_type_visitor<Solver>(solver, var_map), expr );
    }

    template < typename Solver >
    class ExpressionSolver {
    public:
      typedef typename expr::logic_expression result_type;
      typedef typename Solver::result_type backend_result_type;
      typedef std::map< unsigned, backend_result_type > VarMap;

      ExpressionSolver()
      {}

      ~ExpressionSolver()
      {}

      void assertion( result_type e ) {
        // std::cerr << "Assertion: " << expr::to_string(e) << '\n';
        solver.assertion( make_result_type(e) );
      }

      void assumption( result_type e ) {
        // std::cerr << "Assumption: " << expr::to_string(e) << '\n';
        solver.assumption( make_result_type(e) );
      }

      bool solve() {
        return solver.solve();
      }

      result_wrapper read_value( result_type var ) {
        // std::cerr << "Read value: " << expr::to_string(var) << '\n';
        return solver.read_value( make_result_type(var) );
      }

      // logic::tag
      result_type operator() ( predtags::false_tag, boost::any arg ) {
        return expr::logic_expression(false);
      }

      result_type operator() ( predtags::true_tag, boost::any arg ) {
        return expr::logic_expression(true);
      }

      result_type operator() ( predtags::not_tag, result_type arg ) {
        return expr::unary_expression<expr::logic_tag, predtags::not_tag>(arg);
      }

      result_type operator() ( predtags::equal_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::equal_tag>(a, b);
      }

      result_type operator() ( predtags::nequal_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::nequal_tag>(a, b);
      }

      result_type operator() ( predtags::and_tag, result_type a, result_type b ) {
        typedef expr::nary_expression<expr::logic_tag, predtags::and_tag> Expr;
        Expr::ContainerType v;
        v.push_back(a);
        v.push_back(b);
        return Expr(v);
      }

      result_type operator() ( predtags::nand_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::nand_tag>(a, b);
      }

      result_type operator() ( predtags::or_tag, result_type a, result_type b ) {
        typedef expr::nary_expression<expr::logic_tag, predtags::or_tag> Expr;
        Expr::ContainerType v;
        v.push_back(a);
        v.push_back(b);
        return Expr(v);
      }

      result_type operator() ( predtags::nor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::nor_tag>(a, b);
      }

      result_type operator() ( predtags::xor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::xor_tag>(a, b);
      }

      result_type operator() ( predtags::xnor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::xnor_tag>(a, b);
      }

      result_type operator() ( predtags::implies_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, predtags::implies_tag>(a, b);
      }

      result_type operator() ( predtags::ite_tag, result_type a, result_type b, result_type c ) {
        return expr::ternary_expression<expr::logic_tag, predtags::ite_tag>(a, b, c);
      }

      result_type operator() ( predtags::var_tag const &tag, boost::any a ) {        
        if ( tag.id == 0 ) {
          throw std::exception();
        }
        return proto::make_expr< proto::tag::terminal, logic::Predicate_Domain >( tag );
      }

      // logic::QF_BV::tag
      result_type operator() ( bvtags::bit0_tag , boost::any arg ) {
        return logic::QF_BV::bit0;
      }

      result_type operator() ( bvtags::bit1_tag , boost::any arg ) {
        return logic::QF_BV::bit1;
      }

      result_type operator() ( bvtags::var_tag const &tag, boost::any a ) {
        if ( tag.id == 0 ) {
          throw std::exception();
        }
        return proto::make_expr< proto::tag::terminal, logic::QF_BV::QF_BV_Domain >( tag );
      }

      result_type operator() ( bvtags::bvnot_tag, result_type a ) {
        return expr::unary_expression<expr::bv_tag, bvtags::bvnot_tag>(a);
      }

      result_type operator() ( bvtags::bvneg_tag, result_type a ) {
        return expr::unary_expression<expr::bv_tag, bvtags::bvneg_tag>(a);
      }

      result_type operator() ( bvtags::bvand_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvand_tag>(a, b);
      }

      result_type operator() ( bvtags::bvnand_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvnand_tag>(a, b);
      }

      result_type operator() ( bvtags::bvor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvor_tag>(a, b);
      }

      result_type operator() ( bvtags::bvnor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvnor_tag>(a, b);
      }

      result_type operator() ( bvtags::bvxor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvxor_tag>(a, b);
      }

      result_type operator() ( bvtags::bvxnor_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvxnor_tag>(a, b);
      }

      result_type operator() ( bvtags::bvshl_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvshl_tag>(a, b);
      }

      result_type operator() ( bvtags::bvshr_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvshr_tag>(a, b);
      }

      result_type operator() ( bvtags::bvashr_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvashr_tag>(a, b);
      }

      result_type operator() ( bvtags::bvcomp_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvcomp_tag>(a, b);
      }

      result_type operator() ( bvtags::bvadd_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvadd_tag>(a, b);
      }

      result_type operator() ( bvtags::bvmul_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvmul_tag>(a, b);
      }

      result_type operator() ( bvtags::bvsub_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvsub_tag>(a, b);
      }

      result_type operator() ( bvtags::bvsrem_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvsrem_tag>(a, b);
      }

      result_type operator() ( bvtags::bvsdiv_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvsdiv_tag>(a, b);
      }

      result_type operator() ( bvtags::bvurem_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvurem_tag>(a, b);
      }

      result_type operator() ( bvtags::bvudiv_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::bvudiv_tag>(a, b);
      }

      result_type operator() ( bvtags::bvuint_tag , boost::any arg ) {
        typedef boost::tuple<unsigned long, unsigned long> Tuple;
        Tuple tuple = boost::any_cast<Tuple>(arg);
        unsigned long value = boost::get<0>(tuple);
        unsigned long width = boost::get<1>(tuple);
        return expr::bv_const<bvtags::bvuint_tag>(value, width);
      }

      result_type operator() ( bvtags::bvsint_tag , boost::any arg ) {
        typedef boost::tuple<long, unsigned long> Tuple;
        Tuple const tuple = boost::any_cast<Tuple>(arg);
        long value = boost::get<0>(tuple);
        unsigned long const width = boost::get<1>(tuple);
        if (    value > std::numeric_limits<int>::max()
             || value < std::numeric_limits<int>::min()
             || (width > 8*sizeof(int) && value < 0)
          ) {
          std::string val(width, '0');
          std::string::reverse_iterator it = val.rbegin();
          for ( unsigned long u = 0; u < width; ++u, ++it ) {
            *it = (value & 1l) ? '1' : '0';
            value >>= 1;
          }
          return expr::bv_const<bvtags::bvbin_tag>::bin(val);
        }
        else {
          return expr::bv_const<bvtags::bvsint_tag>(static_cast<unsigned long>(value), width);
        }
      }

      result_type operator() ( bvtags::bvbin_tag , boost::any arg ) {
        std::string val = boost::any_cast<std::string>(arg);
        return expr::bv_const<bvtags::bvbin_tag>::bin(val);
      }

      result_type operator() ( bvtags::bvhex_tag , boost::any arg ) {
        std::string val = boost::any_cast<std::string>(arg);
        return expr::bv_const<bvtags::bvhex_tag>::hex(val);
      }

      result_type operator() ( bvtags::bvslt_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvslt_tag>(a, b);
      }

      result_type operator() ( bvtags::bvsgt_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvsgt_tag>(a, b);
      }

      result_type operator() ( bvtags::bvsle_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvsle_tag>(a, b);
      }

      result_type operator() ( bvtags::bvsge_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvsge_tag>(a, b);
      }

      result_type operator() ( bvtags::bvult_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvult_tag>(a, b);
      }

      result_type operator() ( bvtags::bvugt_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvugt_tag>(a, b);
      }

      result_type operator() ( bvtags::bvule_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvule_tag>(a, b);
      }

      result_type operator() ( bvtags::bvuge_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::logic_tag, bvtags::bvuge_tag>(a, b);
      }

      result_type operator() ( bvtags::concat_tag, result_type a, result_type b ) {
        return expr::binary_expression<expr::bv_tag, bvtags::concat_tag>(a, b);
      }

      result_type operator() ( bvtags::extract_tag const &,
                               unsigned long upper,
                               unsigned long lower,
                               result_type e ) {
        unsigned long const width = upper - lower;
        return expr::extract_expression<bvtags::extract_tag>(upper, width, e);
      }
      result_type operator() ( bvtags::zero_extend_tag const &,
                               unsigned long width,
                               result_type e ) {
        return expr::extend_expression<bvtags::zero_extend_tag>(width, e);
      }

      result_type operator() ( bvtags::sign_extend_tag const &,
                               unsigned long width,
                               result_type e ) {
        return expr::extend_expression<bvtags::sign_extend_tag>(width, e);
      }

      // logic::Array::tag
      result_type operator() ( arraytags::array_var_tag const &tag,
                               boost::any args ) {
        if ( tag.id == 0 ) {
          throw std::exception();
        }
        return proto::make_expr< proto::tag::terminal, logic::Array::Array_Domain >( tag );
      }

      result_type operator() ( arraytags::select_tag const &,
                               result_type array,
                               result_type index ) {
        return expr::select_expression( array, index );
      }

      result_type operator() ( arraytags::store_tag const &,
                               result_type array,
                               result_type index,
                               result_type value ) {
        return expr::store_expression( array, index, value );
      }

      // logic::QF_UF::tag
      result_type operator() ( uftags::function_var_tag const &tag,
                               boost::any args ) {
        if ( tag.id == 0 ) {
          throw std::exception();
        }
        return proto::make_expr< proto::tag::terminal, logic::QF_UF::UninterpretedFunction_Domain >( tag );
      }

      result_type operator() ( proto::tag::function const &,
                               result_type func_decl ) {
        typedef expr::nary_expression<expr::uf_tag, proto::tag::function> Func;
        Func::ContainerType v;
        v.push_back( func_decl );
        return Func(v);
      }

      result_type operator() ( proto::tag::function const &,
                               result_type func_decl,
                               result_type arg) {
        typedef expr::nary_expression<expr::uf_tag, proto::tag::function> Func;
        Func::ContainerType v;
        v.push_back(func_decl);
        v.push_back( arg );
        return Func(v);
      }
      
      result_type operator() ( proto::tag::function const &,
                               result_type func_decl,
                               result_type arg1,
                               result_type arg2) {
        typedef expr::nary_expression<expr::uf_tag, proto::tag::function> Func;
        Func::ContainerType v;
        v.push_back( func_decl );
        v.push_back( arg1 );
        v.push_back( arg2 );
        return Func(v);
      }

      result_type operator() ( proto::tag::function const &,
                               result_type func_decl,
                               result_type arg1,
                               result_type arg2,
                               result_type arg3) {
        typedef expr::nary_expression<expr::uf_tag, proto::tag::function> Func;
        Func::ContainerType v;
        v.push_back( func_decl );
        v.push_back( arg1 );
        v.push_back( arg2 );
        v.push_back( arg3 );
        return Func(v);
      }

      // Fallback operators
      template <typename TagT>
      result_type operator() (TagT tag, boost::any args ) {
        assert( false );
        return false;
      }

      template <typename TagT>
      result_type operator() (TagT tag, result_type a ) {
        assert( false );
        return false;
      }

      template <typename TagT>
      result_type operator() (TagT tag, result_type a, result_type b) {
        assert( false );
        return false;
      }

      template <typename TagT>
      result_type operator() (TagT tag, result_type a, result_type b, result_type c) {
        assert( false );
        return false;
      }

      /* pseudo command */
      void command ( ExpressionSolver const & ) { };

    private:
      inline backend_result_type make_result_type( result_type e ) {
        return make_backend_result_type<Solver>(solver, var_map, e);
      }

      Solver solver;
      VarMap var_map;
    }; // ExpressionSolver

  } // solver
} // metaSMT
