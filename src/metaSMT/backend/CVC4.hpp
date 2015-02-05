#pragma once

#include "../tags/QF_BV.hpp"
#include "../result_wrapper.hpp"

#include <cvc4/cvc4.h>

#include <boost/mpl/map/map40.hpp>
#include <boost/any.hpp>
#include <boost/tuple/tuple.hpp>
#include <list>

namespace metaSMT {
  namespace solver {
    namespace predtags = ::metaSMT::logic::tag;
    namespace bvtags = ::metaSMT::logic::QF_BV::tag;

    /**
     * @ingroup Backend
     * @class CVC4 CVC4.hpp metaSMT/backend/CVC4.hpp
     * @brief The CVC4 backend
     */
    class CVC4 {
    public:
      typedef ::CVC4::Expr result_type;
      typedef std::list< ::CVC4::Expr > Exprs;

      CVC4()
        : exprManager_( )
        , engine_( &exprManager_ )
        , isPushed_( false )
      {
        engine_.setOption("incremental", true);
        engine_.setOption("produce-models", true);
      }

      ~CVC4() {
      }

      void assertion( result_type e ) {
        assertions_.push_back( e );
      }

      void assumption( result_type e ) {
        assumptions_.push_back( e );
      }

      bool solve() {
        removeOldAssumptions();
        pushAssertions();
        pushAssumptions();
        
        return engine_.checkSat().isSat();
      }

      result_wrapper read_value(result_type var) {
      
        ::CVC4::Expr value = engine_.getValue(var);
        ::CVC4::Type type = value.getType();

        if (type.isBoolean()) {
          return value.getConst<bool>();
        }

        //case BITVECTOR_TYPE:
        //  {
        //    unsigned long long const value = getBVUnsignedLongLong(cex);
        //    unsigned const width = getBVLength(cex);
        //    boost::dynamic_bitset<> bv(width, value);
        //    std::string str; to_string(bv, str);
        //    return result_wrapper(str);
        //  }
        //  break;
        //case ARRAY_TYPE:
        //case UNKNOWN_TYPE:
        //  assert( false );
        //  break;
        //}
        return result_wrapper( false );
      }

      // predtags
      result_type operator()( predtags::var_tag const & var, boost::any args ) {
        return exprManager_.mkVar(exprManager_.booleanType());
      }

      result_type operator()( predtags::false_tag , boost::any arg ) {
        return exprManager_.mkConst(false);
      }

      result_type operator()( predtags::true_tag , boost::any arg ) {
        return exprManager_.mkConst(true);
      }

      result_type operator()( predtags::not_tag , result_type e ) {
        return exprManager_.mkExpr(::CVC4::kind::NOT, e);
      }

      result_type operator()( predtags::ite_tag tag
                              , result_type a, result_type b, result_type c ) {
        return exprManager_.mkExpr(::CVC4::kind::ITE, a, b, c);
      }

      // bvtags
      /*
      result_type operator()( bvtags::var_tag const & var, boost::any args ) {
        assert ( var.width != 0 );
        Type bv_ty = vc_bvType(vc, var.width);
        char buf[64];
        sprintf(buf, "var_%u", var.id);
        return vc_varExpr(vc, buf, bv_ty);
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
          return vc_bvConstExprFromStr(vc, val.c_str());
        }
        else {
          return vc_bvConstExprFromLL(vc, width, value);
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
          return vc_bvConstExprFromStr(vc, val.c_str());
        }
        else {
          return vc_bvConstExprFromLL(vc, width, static_cast<unsigned long>(value));
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
        return vc_bvConstExprFromStr(vc, bin.c_str());
      }

      result_type operator()( bvtags::bvnot_tag , result_type e ) {
        return vc_bvNotExpr(vc, e);
      }

      result_type operator()( bvtags::bvneg_tag , result_type e ) {
        return vc_bvUMinusExpr(vc, e);
      }

      result_type operator()( bvtags::bvcomp_tag , result_type a, result_type b ) {
        ::CVC4::Expr comp = vc_eqExpr(vc, a, b);
        return vc_boolToBVExpr(vc, comp);
      }

      result_type operator()( bvtags::bvshl_tag, result_type a, result_type b ) {
        return vc_bvVar32LeftShiftExpr(vc, b, a);
      }

      result_type operator()( bvtags::bvshr_tag, result_type a, result_type b ) {
        return vc_bvVar32RightShiftExpr(vc, b, a);
      }

      result_type operator()( bvtags::extract_tag const &
        , unsigned long upper, unsigned long lower
        , result_type e) {
        return vc_bvExtract(vc, e, upper, lower);
      }

      result_type operator()( bvtags::zero_extend_tag const &
        , unsigned long width
        , result_type e) {
        std::string s(width, '0');
        ::CVC4::Expr zeros = vc_bvConstExprFromStr(vc, s.c_str());
        return vc_bvConcatExpr(vc, zeros, e);
      }

      result_type operator()( bvtags::sign_extend_tag const &
        , unsigned long width
        , result_type e) {
        unsigned long const current_width = getBVLength(e);
        return vc_bvSignExtend(vc, e, current_width + width);
      }
      */

      result_type operator()( predtags::equal_tag const &
                             , result_type a
                             , result_type b) {
        if (a.getType().isBoolean() && b.getType().isBoolean() ) {
          return exprManager_.mkExpr(::CVC4::kind::IFF, a, b);
        } else {
          return exprManager_.mkExpr(::CVC4::kind::EQUAL, a, b);
        }
      }

      result_type operator()( predtags::nequal_tag const &
                             , result_type a
                             , result_type b) {
        return exprManager_.mkExpr(::CVC4::kind::DISTINCT, a, b);
      }

      result_type operator()( predtags::distinct_tag const &
                             , result_type a
                             , result_type b) {
        return exprManager_.mkExpr(::CVC4::kind::DISTINCT, a, b);
      }

      ////////////////////////
      // Fallback operators //
      ////////////////////////

      template <typename TagT>
      result_type operator() (TagT tag, boost::any args ) {
        assert( false );
        return exprManager_.mkConst(false);
      }

      template< ::CVC4::kind::Kind_t KIND_ >
      struct Op2 {
        static result_type exec(::CVC4::ExprManager& em, ::CVC4::Expr x,
          ::CVC4::Expr y) 
        {
          return em.mkExpr(KIND_, x, y); 
        }
      };

      template< ::CVC4::kind::Kind_t KIND_ >
      struct NotOp2 {
        static result_type exec(::CVC4::ExprManager& em, ::CVC4::Expr x,
          ::CVC4::Expr y) 
        {
          return em.mkExpr(::CVC4::kind::NOT, em.mkExpr(KIND_, x, y)); 
        }
      };

      template <typename TagT>
      result_type operator() (TagT tag, result_type a, result_type b) {
        namespace mpl = boost::mpl;
        using namespace ::CVC4::kind;

        typedef mpl::map29<
          // binary Logic tags
          mpl::pair<predtags::and_tag,     Op2<AND> >
        , mpl::pair<predtags::nand_tag,    NotOp2<AND> >
        , mpl::pair<predtags::or_tag,      Op2<OR> >
        , mpl::pair<predtags::nor_tag,     NotOp2<OR> >
        , mpl::pair<predtags::xor_tag,     Op2<XOR> >
        , mpl::pair<predtags::xnor_tag,    NotOp2<XOR> >
        , mpl::pair<predtags::implies_tag, Op2<IMPLIES> >
        // binary QF_BV tags
        , mpl::pair<bvtags::bvand_tag,     Op2<BITVECTOR_AND> >
        , mpl::pair<bvtags::bvnand_tag,    Op2<BITVECTOR_NAND> >
        , mpl::pair<bvtags::bvor_tag,      Op2<BITVECTOR_OR> >
        , mpl::pair<bvtags::bvnor_tag,     Op2<BITVECTOR_NOR> >
        , mpl::pair<bvtags::bvxor_tag,     Op2<BITVECTOR_XOR> >
        , mpl::pair<bvtags::bvxnor_tag,    Op2<BITVECTOR_XNOR> >
        , mpl::pair<bvtags::bvadd_tag,     Op2<BITVECTOR_PLUS> >
        , mpl::pair<bvtags::bvsub_tag,     Op2<BITVECTOR_SUB> >
        , mpl::pair<bvtags::bvmul_tag,     Op2<BITVECTOR_MULT> >
        , mpl::pair<bvtags::bvudiv_tag,    Op2<BITVECTOR_UDIV> >
        , mpl::pair<bvtags::bvurem_tag,    Op2<BITVECTOR_UREM> >
        , mpl::pair<bvtags::bvsdiv_tag,    Op2<BITVECTOR_SDIV> >
        , mpl::pair<bvtags::bvsrem_tag,    Op2<BITVECTOR_SREM> >
        , mpl::pair<bvtags::bvslt_tag,     Op2<BITVECTOR_SLT> >
        , mpl::pair<bvtags::bvsle_tag,     Op2<BITVECTOR_SLE> >
        , mpl::pair<bvtags::bvsgt_tag,     Op2<BITVECTOR_SGT> >
        , mpl::pair<bvtags::bvsge_tag,     Op2<BITVECTOR_SGE> >
        , mpl::pair<bvtags::bvult_tag,     Op2<BITVECTOR_ULT> >
        , mpl::pair<bvtags::bvule_tag,     Op2<BITVECTOR_ULE> >
        , mpl::pair<bvtags::bvugt_tag,     Op2<BITVECTOR_UGT> >
        , mpl::pair<bvtags::bvuge_tag,     Op2<BITVECTOR_UGE> >
        , mpl::pair<bvtags::concat_tag,    Op2<BITVECTOR_CONCAT> >
        // , mpl::pair<bvtags::bvashr_tag,    Op2<BITVECTOR_ASHR> >
        > Opcode_Map;

        typedef
          typename mpl::has_key< Opcode_Map, TagT >::type
          has_key;

        if (has_key::value ) {
          typedef typename mpl::eval_if<
            has_key
          , mpl::at< Opcode_Map, TagT >
          , mpl::identity< Op2<UNDEFINED_KIND> >
          >::type opcode;
          return opcode::exec(exprManager_, a, b);
        }
        else {
          // std::cerr << "unknown operator: " << tag << std::endl;
          assert(false && "unknown operator");
        }
        return exprManager_.mkConst(false);
      }

      template <typename TagT>
      result_type operator() (TagT tag, result_type a, result_type b, result_type c) {
        assert( false );
        return exprManager_.mkConst(false);
      }

      // pseudo command
      void command ( CVC4 const & ) { };

    private:
      void removeOldAssumptions() {
        if (isPushed_) {
          engine_.pop();
          isPushed_ = false;
        }
      }

      void pushAssumptions() {
        engine_.push();
        isPushed_ = true;

        applyAssertions(assumptions_);
        assumptions_.clear();
      }

      void pushAssertions() {
        applyAssertions(assertions_);
        assertions_.clear();
      }

      void applyAssertions(Exprs const& expressions) {
        for ( Exprs::const_iterator it = expressions.begin(),
              ie = expressions.end(); it != ie; ++it ) {
          engine_.assertFormula(*it);
        }
      }

    private:
      ::CVC4::ExprManager exprManager_;
      ::CVC4::SmtEngine engine_;
      Exprs assumptions_;
      Exprs assertions_;
      bool isPushed_;
    }; // class CVC4

  } // solver
} // metaSMT
