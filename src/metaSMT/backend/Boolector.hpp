#pragma once

#include "../tags/QF_BV.hpp"
#include "../tags/Array.hpp"
#include "../result_wrapper.hpp"

extern "C" {
#include <boolector.h>
}

#include <iostream>
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
     * @class Boolector Boolector.hpp metaSMT/backend/Boolector.hpp
     * @brief The Boolector backend 
     */
    class Boolector {

      struct BoolectorAssertion : public std::runtime_error {
        BoolectorAssertion(const char* what)
          : std::runtime_error(what) {}
      };

      static void _boolector_error(int ec) {
        throw BoolectorAssertion("internal error in boolector");
      }

      public:
        typedef BtorNode* result_type;

        result_type ptr(result_type expr) {
          _exprs.push_back(expr);
          return expr;
        }
      
        Boolector ()
        {
          _btor = boolector_new();
          boolector_enable_model_gen(_btor);
          boolector_enable_inc_usage(_btor);
          boolector_abort_function(&Boolector::_boolector_error);
        }

        ~Boolector() {
          for( std::list<result_type>::iterator ite = _exprs.begin(); ite!=_exprs.end(); ++ite)
          {
            boolector_release(_btor, *ite);
          }
          boolector_delete(_btor);
        }

        void assertion( result_type e ) {
          boolector_assert(_btor, e);
        }

        void assumption( result_type e ) {
          boolector_assume(_btor, e);
        }

        bool solve() {
          return boolector_sat(_btor) == BOOLECTOR_SAT;
        }

        result_wrapper read_value(result_type var)
        {
          char* value = boolector_bv_assignment(_btor, var);
          std::string s(value);
          boolector_free_bv_assignment(_btor, value);
          return result_wrapper(s);
        }

        result_type operator() (predtags::var_tag const & var, boost::any args )
        {
          return ptr(boolector_var(_btor, 1, NULL));
        }

        result_type operator() (predtags::false_tag , boost::any arg ) {
          return ptr(boolector_false(_btor));
        }

        result_type operator() (predtags::true_tag , boost::any arg ) {
          return ptr(boolector_true(_btor));
        }

        result_type operator() (predtags::not_tag , result_type a) {
          return ptr(boolector_not(_btor, a) );
        }


        result_type operator() (bvtags::var_tag const & var, boost::any args )
        {
          assert ( var.width != 0 );
          return ptr(boolector_var(_btor, var.width, NULL));
        }

        result_type operator() (bvtags::bit0_tag , boost::any arg ) {
          return ptr(boolector_false(_btor));
        }

        result_type operator() (bvtags::bit1_tag , boost::any arg ) {
          return ptr(boolector_true(_btor));
        }

        result_type operator() (bvtags::bvuint_tag , boost::any arg ) {
          typedef boost::tuple<unsigned long, unsigned long> P;
          P p = boost::any_cast<P>(arg);
          //std::cout << "bvuint "<< p << std::endl;
          unsigned long value = boost::get<0>(p);
          unsigned long width = boost::get<1>(p);

          if ( value > std::numeric_limits<unsigned>::max() ) {
            std::string val (width, '0');

            std::string::reverse_iterator sit = val.rbegin();

            for (unsigned long i = 0; i < width; i++, ++sit) {
              *sit = (value & 1ul) ? '1':'0';
              value >>= 1;
            }
            return ptr( boolector_const(_btor, val.c_str()) );
          } else {
            return ptr(boolector_unsigned_int(_btor, value , width ));
          }
        }

        result_type operator() (bvtags::bvsint_tag , boost::any arg ) {
          typedef boost::tuple<long, unsigned long> P;
          P const p = boost::any_cast<P>(arg);
          long value = boost::get<0>(p);
          unsigned long const width = boost::get<1>(p);

          if (  value > std::numeric_limits<int>::max()
             || value < std::numeric_limits<int>::min()
          ) {
            std::string val (width, '0');

            std::string::reverse_iterator sit = val.rbegin();

            for (unsigned long i = 0; i < width; i++, ++sit) {
              *sit = (value & 1l) ? '1':'0';
              value >>= 1;
            }
            return ptr( boolector_const(_btor, val.c_str()) );
          } else {
            return ptr( boolector_int(_btor, value, width) );
          }
        }

        result_type operator() (bvtags::bvbin_tag , boost::any arg ) {
          std::string val = boost::any_cast<std::string>(arg);
          return ptr(boolector_const(_btor, val.c_str()));
        }

        result_type operator() (bvtags::bvhex_tag , boost::any arg ) {
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
          return ptr(boolector_const(_btor, bin.c_str()));
        }

        result_type operator() (bvtags::bvnot_tag , result_type a ) {
          return ptr(boolector_not(_btor, a));
        }

        result_type operator() (bvtags::bvneg_tag , result_type a ) {
          return ptr(boolector_neg(_btor, a));
        }

        result_type operator() (bvtags::extract_tag const &
            , unsigned long upper, unsigned long lower
            , result_type e)
        {
          return ptr(boolector_slice(_btor, e, upper, lower));
        }

        result_type operator() (bvtags::zero_extend_tag const &
            , unsigned long width
            , result_type e)
        {
          return ptr(boolector_uext(_btor, e, width));
        }

        result_type operator() (bvtags::sign_extend_tag const &
            , unsigned long width
            , result_type e)
        {
          return ptr(boolector_sext(_btor, e, width));
        }

        result_type operator() (arraytags::array_var_tag const & var
                                , boost::any args )
        {
          return ptr(boolector_array(_btor, var.elem_width, var.index_width, NULL));
        }

        result_type operator() (arraytags::select_tag const &
                                , result_type array
                                , result_type index) {
          return ptr(boolector_read(_btor, array, index));
        }

        result_type operator() (arraytags::store_tag const &
                                , result_type array
                                , result_type index
                                , result_type value) {
          return ptr(boolector_write(_btor, array, index, value));
        }

        result_type operator() (predtags::ite_tag tag, result_type a, result_type b, result_type c) {
          return ptr(boolector_cond(_btor, a, b, c));
        }

        ////////////////////////
        // Fallback operators //
        ////////////////////////

        template <typename TagT>
        result_type operator() (TagT tag, boost::any args ) {
          return ptr(boolector_false(_btor));
        }


        template <typename TagT>
        result_type operator() (TagT tag, result_type a ) {
          return ptr(boolector_false(_btor));
        }

        template< result_type (*FN) (Btor*, result_type, result_type) >
        struct Btor_F2 {
          static result_type exec(Btor* b , result_type x, result_type y)
          { return (*FN)(b,x,y);}
        };

        template <typename TagT>
        result_type operator() (TagT tag, result_type a, result_type b) {
          namespace mpl = boost::mpl;

          typedef mpl::map35<
          // binary Logic tags
            mpl::pair<predtags::equal_tag,   Btor_F2<&boolector_eq> >
          , mpl::pair<predtags::nequal_tag,  Btor_F2<&boolector_ne> >
          , mpl::pair<predtags::and_tag,     Btor_F2<&boolector_and> >
          , mpl::pair<predtags::nand_tag,    Btor_F2<&boolector_nand> >
          , mpl::pair<predtags::or_tag,      Btor_F2<&boolector_or> >
          , mpl::pair<predtags::nor_tag,     Btor_F2<&boolector_nor> >
          , mpl::pair<predtags::xor_tag,     Btor_F2<&boolector_xor> >
          , mpl::pair<predtags::xnor_tag,    Btor_F2<&boolector_xnor> >
          , mpl::pair<predtags::implies_tag, Btor_F2<&boolector_implies> >
          // binary QF_BV tags
          , mpl::pair<bvtags::bvand_tag,     Btor_F2<&boolector_and> >
          , mpl::pair<bvtags::bvnand_tag,    Btor_F2<&boolector_nand> >
          , mpl::pair<bvtags::bvor_tag,      Btor_F2<&boolector_or> >
          , mpl::pair<bvtags::bvnor_tag,     Btor_F2<&boolector_nor> >
          , mpl::pair<bvtags::bvxor_tag,     Btor_F2<&boolector_xor> >
          , mpl::pair<bvtags::bvxnor_tag,    Btor_F2<&boolector_xnor> >
          , mpl::pair<bvtags::bvadd_tag,     Btor_F2<&boolector_add> >
          , mpl::pair<bvtags::bvsub_tag,     Btor_F2<&boolector_sub> >
          , mpl::pair<bvtags::bvmul_tag,     Btor_F2<&boolector_mul> >
          , mpl::pair<bvtags::bvudiv_tag,    Btor_F2<&boolector_udiv> >
          , mpl::pair<bvtags::bvurem_tag,    Btor_F2<&boolector_urem> >
          , mpl::pair<bvtags::bvsdiv_tag,    Btor_F2<&boolector_sdiv> >
          , mpl::pair<bvtags::bvsrem_tag,    Btor_F2<&boolector_srem> >
          , mpl::pair<bvtags::bvcomp_tag,    Btor_F2<&boolector_eq > >
          , mpl::pair<bvtags::bvslt_tag,     Btor_F2<&boolector_slt > >
          , mpl::pair<bvtags::bvsle_tag,     Btor_F2<&boolector_slte > >
          , mpl::pair<bvtags::bvsgt_tag,     Btor_F2<&boolector_sgt > >
          , mpl::pair<bvtags::bvsge_tag,     Btor_F2<&boolector_sgte > >
          , mpl::pair<bvtags::bvult_tag,     Btor_F2<&boolector_ult > >
          , mpl::pair<bvtags::bvule_tag,     Btor_F2<&boolector_ulte > >
          , mpl::pair<bvtags::bvugt_tag,     Btor_F2<&boolector_ugt > >
          , mpl::pair<bvtags::bvuge_tag,     Btor_F2<&boolector_ugte > >
          , mpl::pair<bvtags::concat_tag,    Btor_F2<&boolector_concat > >
          , mpl::pair<bvtags::bvshl_tag,     Btor_F2<&boolector_sll > >
          , mpl::pair<bvtags::bvshr_tag,     Btor_F2<&boolector_srl > >
          , mpl::pair<bvtags::bvashr_tag,    Btor_F2<&boolector_sra > >
          > Opcode_Map;

          typedef
            typename mpl::has_key< Opcode_Map, TagT >::type
          _has_key;

          if (_has_key::value ) {
          typedef typename mpl::eval_if<
            _has_key
            , mpl::at< Opcode_Map, TagT >
            , mpl::identity< Btor_F2<boolector_and> >
            >::type opcode;
          return ptr(opcode::exec(_btor, a, b));
          } else {
            std::cout << "unknown operator: " << tag << std::endl;

            assert(false && "unknown operator");
            return ptr(boolector_false(_btor));
          }
        }


        template <typename TagT>
        result_type operator() (TagT tag, result_type a, result_type b, result_type c) {
          return ptr(boolector_false(_btor));
        }


        /* pseudo command */
        void command ( Boolector const & ) { };

      private:
        Btor *_btor;
        std::list<result_type> _exprs;
    };

    /**@}*/

  } // namespace solver
} // namespace metaSMT

//  vim: ft=cpp:ts=2:sw=2:expandtab
