#pragma once

#include "../tags/QF_BV.hpp"
#include "../tags/Array.hpp"
#include "../result_wrapper.hpp"

extern "C" {
#include <stp/c_interface.h>
}

#include <boost/mpl/map/map40.hpp>
#include <boost/any.hpp>
#include <boost/tuple/tuple.hpp>
#include <list>

namespace metaSMT {
  namespace solver {
    namespace predtags = ::metaSMT::logic::tag;
    namespace bvtags = ::metaSMT::logic::QF_BV::tag;
    namespace arraytags = ::metaSMT::logic::Array::tag;

    /**
     * @ingroup Backend
     * @class STP STP.hpp metaSMT/backend/STP.hpp
     * @brief The STP backend
     */
    class STP {
    public:
      typedef Expr result_type;
      typedef std::list< Expr > Exprs;

      result_type ptr(Expr expr) {
        exprs.push_back(expr);
        return expr;
      }

      STP()
        : vc( vc_createValidityChecker() )
      {
        make_division_total( vc );
      }

      ~STP() {
        for( Exprs::iterator it = exprs.begin(), ie = exprs.end();
             it != ie; ++it ) {
          vc_DeleteExpr(*it);
        }
        vc_Destroy(vc);
      }

      void assertion( result_type e ) {
        assertions.push_back( e );
      }

      void assumption( result_type e ) {
        assumptions.push_back( e );
      }

      bool solve() {
        enum SolverResult {
          INVALID = 0
        , VALID = 1
        , ERROR = 2
        , TIMEOUT = 3
        };

        Expr e = ptr(vc_trueExpr( vc ));
        for ( Exprs::const_iterator it = assertions.begin(), ie = assertions.end();
              it != ie; ++it ) {
          e = ptr(vc_andExpr(vc, e, *it));
        }
        for ( Exprs::const_iterator it = assumptions.begin(), ie = assumptions.end();
              it != ie; ++it ) {
          e = ptr(vc_andExpr(vc, e, *it));
        }

        // negate formula
        e = ptr(vc_notExpr(vc, e));
        // vc_printExpr(vc, e);

        vc_push( vc );
        bool sat = false;
        switch ( vc_query(vc, e) ) {
        case VALID:
          // negated formula is tautologie
          sat = false;
          break;
        case INVALID:
          // otherwise
          sat = true;
          break;
        default:
          assert( false && "STP solver returns neither SAT nor UNSAT!");
          // exception
        }
        vc_pop( vc );
        // std::cerr << "SAT? " << sat << '\n';
        assumptions.clear();

        return sat;
      }

      result_wrapper read_value(result_type var) {
        Expr cex = ptr(vc_getCounterExample(vc, var));
        // vc_printExpr(vc, cex);

        switch ( getType(var) ) {
        case BOOLEAN_TYPE:
          {
            int const value = vc_isBool(cex);
            if ( value == 1 ) {
              return result_wrapper( true );
            }
            else if ( value == 0 ) {
              return result_wrapper( false );
            }
          }
          break;
        case BITVECTOR_TYPE:
          {
            unsigned long long const value = getBVUnsignedLongLong(cex);
            unsigned const width = getBVLength(cex);
            boost::dynamic_bitset<> bv(width, value);
            std::string str; to_string(bv, str);
            return result_wrapper(str);
          }
          break;
        case ARRAY_TYPE:
        case UNKNOWN_TYPE:
          assert( false );
          break;
        }
        return result_wrapper( false );
      }

      // predtags
      result_type operator()( predtags::var_tag const & var, boost::any args ) {
        Type bool_ty = vc_boolType(vc);
        char buf[64];
        sprintf(buf, "var_%u", var.id);
        return ptr(vc_varExpr(vc, buf, bool_ty));
      }

      result_type operator()( predtags::false_tag , boost::any arg ) {
        return ptr(vc_falseExpr(vc));
      }

      result_type operator()( predtags::true_tag , boost::any arg ) {
        return ptr(vc_trueExpr(vc));
      }

      result_type operator()( predtags::not_tag , result_type e ) {
        return ptr(vc_notExpr(vc, e));
      }

      result_type operator()( predtags::and_tag,
                              std::vector<result_type> const &vs) {
        std::size_t const num_elm = vs.size();
        Expr *exprs = new Expr[num_elm];
        for (unsigned u = 0; u < num_elm; ++u)
          exprs[u] = vs[u];
        return ptr(vc_andExprN(vc, exprs, num_elm));
      }

      result_type operator()( predtags::or_tag,
                              std::vector<result_type> const &vs) {
        std::size_t const num_elm = vs.size();
        Expr *exprs = new Expr[num_elm];
        for (unsigned u = 0; u < num_elm; ++u)
          exprs[u] = vs[u];
        return ptr(vc_orExprN(vc, exprs, num_elm));
      }

      result_type operator()( predtags::ite_tag tag
                              , result_type a, result_type b, result_type c ) {
        return ptr(vc_iteExpr(vc, a, b, c));
      }

      // bvtags
      result_type operator()( bvtags::var_tag const & var, boost::any args ) {
        assert ( var.width != 0 );
        Type bv_ty = vc_bvType(vc, var.width);
        char buf[64];
        sprintf(buf, "var_%u", var.id);
        return ptr(vc_varExpr(vc, buf, bv_ty));
      }

      result_type operator()( bvtags::bit0_tag , boost::any arg ) {
        return (vc_bvConstExprFromInt(vc, 1, 0)); // No ptr()
      }

      result_type operator()( bvtags::bit1_tag , boost::any arg ) {
        return (vc_bvConstExprFromInt(vc, 1, 1)); // No ptr()
      }

      result_type operator()( bvtags::bvuint_tag , boost::any arg ) {
        typedef boost::tuple<unsigned long, unsigned long> Tuple;
        Tuple tuple = boost::any_cast<Tuple>(arg);
        unsigned long value = boost::get<0>(tuple);
        unsigned long width = boost::get<1>(tuple);

        if ( width > 8*sizeof(unsigned long) ) {
          std::string val (width, '0');

          std::string::reverse_iterator sit = val.rbegin();
          for (unsigned long i = 0; i < width; i++, ++sit) {
            *sit = (value & 1ul) ? '1':'0';
            value >>= 1;
          }
          return ptr(vc_bvConstExprFromStr(vc, val.c_str()));
        }
        else {
          return ptr(vc_bvConstExprFromLL(vc, width, value));
        }
      }

      result_type operator()( bvtags::bvsint_tag , boost::any arg ) {
        typedef boost::tuple<long, unsigned long> Tuple;
        Tuple tuple = boost::any_cast<Tuple>(arg);
        long value = boost::get<0>(tuple);
        unsigned long width = boost::get<1>(tuple);

        if ( width > 8*sizeof(unsigned long)
             || value > std::numeric_limits<long int>::max()
             || value < std::numeric_limits<long int>::min()
        ) {
          std::string val (width, '0');

          std::string::reverse_iterator sit = val.rbegin();
          for (unsigned long i = 0; i < width; i++, ++sit) {
            *sit = (value & 1l) ? '1':'0';
            value >>= 1;
          }
          return ptr(vc_bvConstExprFromStr(vc, val.c_str()));
        }
        else {
          return ptr(vc_bvConstExprFromLL(vc, width, static_cast<unsigned long>(value)));
        }
      }

      result_type operator()( bvtags::bvbin_tag , boost::any arg ) {
        std::string val = boost::any_cast<std::string>(arg);
        return (vc_bvConstExprFromStr(vc, val.c_str()));
      }

      result_type operator()( bvtags::bvhex_tag , boost::any arg ) {
        std::string hex = boost::any_cast<std::string>(arg);
        std::string bin (hex.size()*4,'\0');

        for (unsigned i = 0; i < hex.size(); ++i) {
          switch ( tolower(hex[i]) ) {
          case '0':
            bin.replace(4*i,4, "0000");
            break;
          case '1':
            bin.replace(4*i,4, "0001");
            break;
          case '2':
            bin.replace(4*i,4, "0010");
            break;
          case '3':
            bin.replace(4*i,4, "0011");
            break;
          case '4':
            bin.replace(4*i,4, "0100");
            break;
          case '5':
            bin.replace(4*i,4, "0101");
            break;
          case '6':
            bin.replace(4*i,4, "0110");
            break;
          case '7':
            bin.replace(4*i,4, "0111");
            break;
          case '8':
            bin.replace(4*i,4, "1000");
            break;
          case '9':
            bin.replace(4*i,4, "1001");
            break;
          case 'a':
            bin.replace(4*i,4, "1010");
            break;
          case 'b':
            bin.replace(4*i,4, "1011");
            break;
          case 'c':
            bin.replace(4*i,4, "1100");
            break;
          case 'd':
            bin.replace(4*i,4, "1101");
            break;
          case 'e':
            bin.replace(4*i,4, "1110");
            break;
          case 'f':
            bin.replace(4*i,4, "1111");
            break;
          }
        }
        //std::cout << bin << std::endl;
        return ptr(vc_bvConstExprFromStr(vc, bin.c_str()));
      }

      result_type operator()( bvtags::bvnot_tag , result_type e ) {
        return ptr(vc_bvNotExpr(vc, e));
      }

      result_type operator()( bvtags::bvneg_tag , result_type e ) {
        return ptr(vc_bvUMinusExpr(vc, e));
      }

      result_type operator()( bvtags::bvcomp_tag , result_type a, result_type b ) {
        Expr comp = ptr(vc_eqExpr(vc, a, b));
        return ptr(vc_boolToBVExpr(vc, comp));
      }

      result_type operator()( bvtags::bvshl_tag, const result_type& a, const result_type& b ) {
        const int w = getBVLength(a);
        return ptr(vc_bvLeftShiftExprExpr(vc, w, a, b));
      }

      result_type operator()( bvtags::bvshr_tag, const result_type& a, const result_type& b ) {
        const int w = getBVLength(a);
        return ptr(vc_bvRightShiftExprExpr(vc, w, a, b));
      }

      result_type operator()( bvtags::bvashr_tag, const result_type& a, const result_type& b ) {
        const int w = getBVLength(a);
        return ptr(vc_bvSignedRightShiftExprExpr(vc, w, a, b));
      }

      result_type operator()( bvtags::extract_tag const &
        , unsigned long upper, unsigned long lower
        , result_type e) {
        return ptr(vc_bvExtract(vc, e, upper, lower));
      }

      result_type operator()( bvtags::zero_extend_tag const &
        , unsigned long width
        , result_type e) {
        std::string s(width, '0');
        Expr zeros = ptr(vc_bvConstExprFromStr(vc, s.c_str()));
        return ptr(vc_bvConcatExpr(vc, zeros, e));
      }

      result_type operator()( bvtags::sign_extend_tag const &
        , unsigned long width
        , result_type e) {
        unsigned long const current_width = getBVLength(e);
        return ptr(vc_bvSignExtend(vc, e, current_width + width));
      }

      result_type operator()( predtags::equal_tag const &
                             , result_type a
                             , result_type b) {
        enum type_t const type_a = getType(a);
        enum type_t const type_b = getType(b);

        // std::cerr << type_a << '\n';
        // std::cerr << type_b << '\n';
        assert( type_a == type_b );

        if ( type_a == BOOLEAN_TYPE && type_b == BOOLEAN_TYPE ) {
          return ptr(vc_iffExpr(vc, a, b));
        }

        return ptr(vc_eqExpr(vc, a, b));
      }

      result_type operator()( predtags::nequal_tag const &
                             , result_type a
                             , result_type b) {
        return ptr(vc_notExpr(vc, operator()(predtags::equal_tag(), a, b)));
      }
      
    
      result_type operator() (arraytags::array_var_tag const & var
                              , boost::any args )
      {
        if (var.id == 0 ) {
          throw std::runtime_error("uninitialized array used");
        }
       
        Type index_sort = vc_bvType(vc, var.index_width);
        Type elem_sort = vc_bvType(vc, var.elem_width);
        Type ty = vc_arrayType(vc, index_sort, elem_sort);

        char buf[64];
        sprintf(buf, "var_%u", var.id);
	
        return(ptr(vc_varExpr(vc, buf, ty)));	

      }

      
      result_type operator() (arraytags::select_tag const &
                              , result_type array
                              , result_type index) {
        return ptr(vc_readExpr(vc, array, index));
      }

      result_type operator() (arraytags::store_tag const &
                              , result_type array
                              , result_type index
                              , result_type value) {
        return ptr(vc_writeExpr(vc, array, index, value));
      }
      

      result_type operator()( predtags::distinct_tag const &
                             , result_type a
                             , result_type b) {
        return ptr(vc_notExpr(vc, operator()(predtags::equal_tag(), a, b)));
      }

      ////////////////////////
      // Fallback operators //
      ////////////////////////

      template <typename TagT>
      result_type operator() (TagT tag, boost::any args ) {
        assert( false );
        return ptr(vc_falseExpr(vc));
      }

      template< result_type (*FN) (VC, Expr, Expr) >
      struct VC_F2 {
        static result_type exec(VC vc, Expr x, Expr y) {
          return (*FN)(vc,x,y);
        }
      };

      template< result_type (*FN) (VC, int, Expr, Expr) >
      struct VC_SIZE_F2 {
        static result_type exec(VC vc, Expr x, Expr y) {
          int const size_x = getBVLength(x);
          int const size_y = getBVLength(y);
          assert( size_x == size_y );
          return (*FN)(vc,size_x,x,y);
        }
      };

      template< result_type (*FN) (VC, Expr, Expr) >
      struct VC_NOT_F2 {
        static result_type exec(VC vc , Expr x, Expr y) {
          return vc_notExpr(vc, (*FN)(vc, x, y));
        }
      };

      template< result_type (*FN) (VC, Expr, Expr) >
      struct VC_BVNOT_F2 {
        static result_type exec(VC vc , Expr x, Expr y) {
          return vc_bvNotExpr(vc, (*FN)(vc, x, y));
        }
      };

      template <typename TagT>
      result_type operator() (TagT tag, result_type a, result_type b) {
        namespace mpl = boost::mpl;

        typedef mpl::map29<
          // binary Logic tags
          mpl::pair<predtags::and_tag,     VC_F2<&vc_andExpr> >
        , mpl::pair<predtags::nand_tag,    VC_NOT_F2<&vc_andExpr> >
        , mpl::pair<predtags::or_tag,      VC_F2<&vc_orExpr> >
        , mpl::pair<predtags::nor_tag,     VC_NOT_F2<&vc_orExpr> >
        , mpl::pair<predtags::xor_tag,     VC_F2<&vc_xorExpr> >
        , mpl::pair<predtags::xnor_tag,    VC_NOT_F2<&vc_xorExpr> >
        , mpl::pair<predtags::implies_tag, VC_F2<&vc_impliesExpr> >
        // binary QF_BV tags
        , mpl::pair<bvtags::bvand_tag,     VC_F2<&vc_bvAndExpr> >
        , mpl::pair<bvtags::bvnand_tag,    VC_BVNOT_F2<&vc_bvAndExpr> >
        , mpl::pair<bvtags::bvor_tag,      VC_F2<&vc_bvOrExpr> >
        , mpl::pair<bvtags::bvnor_tag,     VC_BVNOT_F2<&vc_bvOrExpr> >
        , mpl::pair<bvtags::bvxor_tag,     VC_F2<&vc_bvXorExpr> >
        , mpl::pair<bvtags::bvxnor_tag,    VC_BVNOT_F2<&vc_bvXorExpr> >
        , mpl::pair<bvtags::bvadd_tag,     VC_SIZE_F2<&vc_bvPlusExpr> >
        , mpl::pair<bvtags::bvsub_tag,     VC_SIZE_F2<&vc_bvMinusExpr> >
        , mpl::pair<bvtags::bvmul_tag,     VC_SIZE_F2<&vc_bvMultExpr> >
        , mpl::pair<bvtags::bvudiv_tag,    VC_SIZE_F2<&vc_bvDivExpr> >
        , mpl::pair<bvtags::bvurem_tag,    VC_SIZE_F2<&vc_bvModExpr> >
        , mpl::pair<bvtags::bvsdiv_tag,    VC_SIZE_F2<&vc_sbvDivExpr> >
        , mpl::pair<bvtags::bvsrem_tag,    VC_SIZE_F2<&vc_sbvRemExpr> >
        , mpl::pair<bvtags::bvslt_tag,     VC_F2<&vc_sbvLtExpr> >
        , mpl::pair<bvtags::bvsle_tag,     VC_F2<&vc_sbvLeExpr> >
        , mpl::pair<bvtags::bvsgt_tag,     VC_F2<&vc_sbvGtExpr> >
        , mpl::pair<bvtags::bvsge_tag,     VC_F2<&vc_sbvGeExpr> >
        , mpl::pair<bvtags::bvult_tag,     VC_F2<&vc_bvLtExpr> >
        , mpl::pair<bvtags::bvule_tag,     VC_F2<&vc_bvLeExpr> >
        , mpl::pair<bvtags::bvugt_tag,     VC_F2<&vc_bvGtExpr> >
        , mpl::pair<bvtags::bvuge_tag,     VC_F2<&vc_bvGeExpr> >
        , mpl::pair<bvtags::concat_tag,    VC_F2<&vc_bvConcatExpr> >
        > Opcode_Map;

        typedef
          typename mpl::has_key< Opcode_Map, TagT >::type
          _has_key;

        if (_has_key::value ) {
          typedef typename mpl::eval_if<
            _has_key
          , mpl::at< Opcode_Map, TagT >
          , mpl::identity< VC_F2<vc_bvAndExpr> >
          >::type opcode;
          return ptr(opcode::exec(vc, a, b));
        }
        else {
          // std::cerr << "unknown operator: " << tag << std::endl;

          assert(false && "unknown operator");
          return ptr(vc_falseExpr(vc));
        }
      }

      template <typename TagT>
      result_type operator() (TagT tag, result_type a, result_type b, result_type c) {
        assert( false );
        return ptr(vc_falseExpr(vc));
      }

      // pseudo command
      void command ( STP const & ) { };

      VC vc;
      Exprs assertions;
      Exprs assumptions;
      Exprs exprs;
    }; // STP

  } // solver
} // metaSMT
