#pragma once

#include "../tags/QF_BV.hpp"
#include "../result_wrapper.hpp"

#include <libsword.h>

#include <boost/mpl/integral_c.hpp>
#include <boost/mpl/map/map40.hpp>
#include <boost/any.hpp>
#include <iostream>
#include <cstdio>



namespace metaSMT {
  namespace solver {

    namespace bvtags = ::metaSMT::logic::QF_BV::tag;
    namespace predtags = ::metaSMT::logic::tag;

    /**
     * @ingroup Backend
     * @class SWORD_Backend SWORD_Backend.hpp metaSMT/backend/SWORD_Backend.hpp
     * @brief SWORD backend
     */
    class SWORD_Backend {
      private:
        template <SWORD::OPCODE OC>
        struct SWORD_Op : public boost::mpl::integral_c<SWORD::OPCODE, OC> {};

      public:
        typedef SWORD::PSignal result_type;

        SWORD_Backend () {
          //_sword.recordTo("/tmp/sword.log");
        }

        /********************
         * predicate logic
         *******************/

        result_type operator() (predtags::var_tag const & var, boost::any args )
        {
          char buf[256];
          sprintf(buf, "pvar_%d", var.id);
          //printf("predicate variable created %s\n", buf);
          return _sword.addVariable(1, buf);
        }

        result_type operator() (predtags::false_tag , boost::any arg ) {
          //printf("false\n");
          return _sword.addConstant(1,0);
        }

        result_type operator() (predtags::true_tag , boost::any arg ) {
          //printf("true\n");
          return _sword.addConstant(1,1);
        }

        // QF_BV tags

        result_type operator() (bvtags::var_tag const & var , boost::any args ) 
        {
          char buf[256];
          sprintf(buf, "var_%d", var.id);
          //printf("variable created %s\n", buf);
          return _sword.addVariable(var.width, buf);
        }

        result_type operator() (bvtags::bit0_tag , boost::any arg ) {
          //printf("bit0\n");
          return _sword.addConstant(1,0);
        }

        result_type operator() (bvtags::bit1_tag , boost::any arg ) {
          //printf("bit1\n");
          return _sword.addConstant(1,1);
        }


        result_type operator() (bvtags::bvbin_tag , boost::any arg ) {
          //printf("bvuint\n");
          return _sword.addBinConstant(boost::any_cast<std::string>(arg));
        }

        result_type operator() (bvtags::bvhex_tag , boost::any arg ) {
          //printf("bvuint\n");
          return _sword.addHexConstant(boost::any_cast<std::string>(arg));
        }

        result_type operator() (bvtags::bvuint_tag , boost::any arg ) {
          typedef boost::tuple<unsigned long, unsigned long> P;
          P p = boost::any_cast<P>(arg);
          //printf("bvuint\n");
          return _sword.addConstant(boost::get<1>(p), boost::get<0>(p));
        }

        result_type operator() (bvtags::bvsint_tag , boost::any arg ) {
          //printf("bvsint\n");
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
            return _sword.addBinConstant(val);
          }
          return _sword.addConstant(width, static_cast<unsigned long>(value) );
        }

        result_type operator() (bvtags::extract_tag const & 
            , unsigned long upper, unsigned long lower
            , result_type e)
        {
          return _sword.addExtract(e, upper, lower);
        }

        result_type operator() (bvtags::zero_extend_tag const & 
            , unsigned long width
            , result_type e)
        {
          return _sword.addZeroExtend(e, width);
        }

        result_type operator() (bvtags::sign_extend_tag const & 
            , unsigned long width
            , result_type e)
        {
          return _sword.addSignExtend(e, width);
        }


        template <typename TagT>
        result_type operator() (TagT tag, boost::any args ) {
          std::cout << tag << std::endl;
          //printf(",0\n");
          //Tag t (tag);
          //std::cout << "SWORD op0: " << t << std::endl;
          return NULL;
        }

        template <typename TagT>
        result_type operator() (TagT tag, result_type a ) {
          return (*this)(tag, a, NULL, NULL);
        }

        template <typename TagT>
        result_type operator() (TagT tag, result_type a, result_type b) {
          return (*this)(tag, a, b, NULL);
        }

        template <typename TagT>
        result_type operator() (TagT tag, result_type a, result_type b, result_type c) {
          namespace mpl = boost::mpl;

          typedef mpl::map40<
            mpl::pair<metaSMT::nil,          SWORD_Op<SWORD::UNKNOWN> >
          // predicate tags
          , mpl::pair<predtags::not_tag,     SWORD_Op<SWORD::NOT> >
          , mpl::pair<predtags::equal_tag,   SWORD_Op<SWORD::EQUAL> >
          , mpl::pair<predtags::nequal_tag,  SWORD_Op<SWORD::NEQUAL> >
          , mpl::pair<predtags::and_tag,     SWORD_Op<SWORD::AND> >
          , mpl::pair<predtags::nand_tag,    SWORD_Op<SWORD::NAND> >
          , mpl::pair<predtags::or_tag,      SWORD_Op<SWORD::OR> >
          , mpl::pair<predtags::nor_tag,     SWORD_Op<SWORD::NOR> >
          , mpl::pair<predtags::xor_tag,     SWORD_Op<SWORD::XOR> >
          , mpl::pair<predtags::xnor_tag,    SWORD_Op<SWORD::XNOR> >
          , mpl::pair<predtags::implies_tag, SWORD_Op<SWORD::IMPLIES> >

          // unary tags
          , mpl::pair<bvtags::bvnot_tag,     SWORD_Op<SWORD::NOT> >
          , mpl::pair<bvtags::bvneg_tag,     SWORD_Op<SWORD::NEG> >

          // binary tags
          , mpl::pair<bvtags::bvand_tag,     SWORD_Op<SWORD::AND> >
          , mpl::pair<bvtags::bvnand_tag,    SWORD_Op<SWORD::NAND> >
          , mpl::pair<bvtags::bvor_tag,      SWORD_Op<SWORD::OR> >
          , mpl::pair<bvtags::bvnor_tag,     SWORD_Op<SWORD::NOR> >
          , mpl::pair<bvtags::bvxor_tag,     SWORD_Op<SWORD::XOR> >
          , mpl::pair<bvtags::bvxnor_tag,    SWORD_Op<SWORD::XNOR> >
          , mpl::pair<bvtags::bvadd_tag,     SWORD_Op<SWORD::ADD> >
          , mpl::pair<bvtags::bvsub_tag,     SWORD_Op<SWORD::SUB> >
          , mpl::pair<bvtags::bvmul_tag,     SWORD_Op<SWORD::MUL> >
          , mpl::pair<bvtags::bvudiv_tag,    SWORD_Op<SWORD::UDIV> >
          , mpl::pair<bvtags::bvurem_tag,    SWORD_Op<SWORD::UREM> >
          , mpl::pair<bvtags::bvsdiv_tag,    SWORD_Op<SWORD::SDIV> >
          , mpl::pair<bvtags::bvsrem_tag,    SWORD_Op<SWORD::SREM> >
          , mpl::pair<bvtags::bvcomp_tag,    SWORD_Op<SWORD::EQUAL> >
          , mpl::pair<bvtags::bvslt_tag,     SWORD_Op<SWORD::SLT> >
          , mpl::pair<bvtags::bvsgt_tag,     SWORD_Op<SWORD::SGT> >
          , mpl::pair<bvtags::bvsle_tag,     SWORD_Op<SWORD::SLE> >
          , mpl::pair<bvtags::bvsge_tag,     SWORD_Op<SWORD::SGE> >
          , mpl::pair<bvtags::bvult_tag,     SWORD_Op<SWORD::ULT> >
          , mpl::pair<bvtags::bvugt_tag,     SWORD_Op<SWORD::UGT> >
          , mpl::pair<bvtags::bvule_tag,     SWORD_Op<SWORD::ULE> >
          , mpl::pair<bvtags::bvuge_tag,     SWORD_Op<SWORD::UGE> >
          , mpl::pair<bvtags::concat_tag,    SWORD_Op<SWORD::CONCAT> >
          , mpl::pair<bvtags::bvshl_tag,     SWORD_Op<SWORD::LSHL> >
          , mpl::pair<bvtags::bvshr_tag,     SWORD_Op<SWORD::LSHR> >
          , mpl::pair<bvtags::bvashr_tag,    SWORD_Op<SWORD::ASHR> >

          //// ternary tags
          , mpl::pair<predtags::ite_tag,       SWORD_Op<SWORD::ITE> >
          > Opcode_Map;

          typedef typename mpl::eval_if<
            typename mpl::has_key< Opcode_Map, TagT >::type
            , mpl::at< Opcode_Map, TagT >
            , mpl::identity< SWORD_Op<SWORD::UNKNOWN> >
            >::type opcode;
          //std::cout << opcode::value << " " << tag << std::endl;
          return _sword.addOperator(opcode::value, a, b, c);
        }

        void assertion( result_type e ) { 
          _sword.addAssertion(e);
        }

        void assumption( result_type e ) { 
          _sword.addAssumption(e);
        }
        
        bool solve() {
          return _sword.solve();
        }

        result_wrapper read_value(result_type var)
        { 
          const std::vector<int> val = _sword.getVariableAssignment(var);
          std::vector<boost::logic::tribool> ret(val.size());
          std::vector<boost::logic::tribool>::iterator it 
            = ret.begin();
          for (unsigned i = 0; i < val.size(); ++i, ++it) {
            switch(val[i]) {
              case 0:  *it = false; break;
              case 1:  *it = true;  break;
              default: *it = boost::logic::indeterminate;
                       //printf("dc\n");
            }
          }
          return result_wrapper(ret);
        }

      /* pseudo command */
      void command ( SWORD_Backend const & ) { };

      private:
        SWORD::sword _sword;
    };

  } // namespace solver
} // namespace metaSMT

//  vim: ft=cpp:ts=2:sw=2:expandtab
