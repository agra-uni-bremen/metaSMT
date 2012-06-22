#pragma once

#include "../tags/QF_BV.hpp"
#include "../result_wrapper.hpp"

#include <mathsat.h>

#include <iostream>
#include <boost/mpl/map.hpp>
#include <boost/tuple/tuple_io.hpp>
#include <boost/lexical_cast.hpp>


namespace metaSMT {
  namespace solver {

    namespace predtags = ::metaSMT::logic::tag;
    namespace bvtags = ::metaSMT::logic::QF_BV::tag;
  
    class mathsat_Context {

      public:
        typedef msat_term result_type;

        mathsat_Context () 
        : env_( msat_create_env() )
        , assumptions_( msat_make_true(env_) )
        {
          msat_add_theory(env_, MSAT_WORD);
        }

        ~mathsat_Context() {
          msat_destroy_env(env_);
        }

        void assertion( result_type e ) { 
          //char * p = msat_to_msat(env_, e);
          //printf(p);
          //free(p);
          msat_assert_formula(env_, e);
        }

        void assumption( result_type e ) { 
          //char * p = msat_to_msat(env_, assumptions_);
          //printf(p);
          //free(p);
          assumptions_ = msat_make_and(env_, e, assumptions_);
        }
        
        bool solve() {
          msat_pop_backtrack_point(env_);
          msat_push_backtrack_point(env_);
          msat_assert_formula(env_, assumptions_);
          bool ret = msat_solve(env_) == MSAT_SAT;
          assumptions_ = msat_make_true(env_);
          return ret;
        }

        result_wrapper read_value(result_type var)
        { 
          result_wrapper ret("X");
          msat_term t = msat_get_model_value(env_, var);
          char* value = msat_to_msat(env_, t);
          if( strcmp(value, "FORMULA true\n" ) == 0 ) {
            //printf("formular true\n");
            return result_wrapper(true);
          } else if( strcmp(value, "FORMULA false\n" ) == 0 ) {
            //printf("formular false\n");
            return result_wrapper(false);
          } else if( strncmp(value, "FORMULA (0d", 11) == 0 ) {
            //printf("formular d\n");
            char* beg = value+11;
            while (*beg && *beg != '_') ++beg;
            std::string widths (value+11, beg);
            ++beg;
            assert(*beg);
            char* end = beg+1;
            while (*end && *end != ')') ++end;
            assert(*end);
            std::string nums(beg, end);
            long width = boost::lexical_cast<long>(widths);
            long num = boost::lexical_cast<long>(nums);

            std::vector<bool> v (width);
            std::vector<bool>::iterator ite =v.begin();
            while (num !=0 ) {
              *ite = (num & 1);
              num>>=1;
              ++ite;
            }
            ret = result_wrapper(v);

            //printf("<%s> %s %s\n", value, widths.c_str(), nums.c_str());
          }
          //std::cout << value << ": " << ret << std::endl;
          free(value);
          return ret;
        }

        result_type operator() (predtags::var_tag const & var, boost::any args )
        {
          char buf[1024];
          sprintf(buf, "var%d", var.id);
          
          msat_decl decl = msat_declare_variable( env_, buf, MSAT_BOOL);
          return msat_make_variable(env_, decl);
        }

        result_type operator() (predtags::false_tag , boost::any arg ) {
          return msat_make_false(env_);
        }

        result_type operator() (predtags::true_tag , boost::any arg ) {
          return msat_make_true(env_);
        }

        result_type operator() (predtags::not_tag , result_type a) {
          return msat_make_not(env_, a) ;
        }


        result_type operator() (predtags::equal_tag , result_type a, result_type b) {
          return msat_make_equal(env_, a, b) ;
        }

        result_type operator() (predtags::nequal_tag , result_type a, result_type b) {
          return msat_make_not(env_, msat_make_equal(env_, a, b) ) ;
        }

        result_type operator() (predtags::and_tag , result_type a, result_type b) {
          return msat_make_and(env_, a, b ) ;
        }

        result_type operator() (predtags::xor_tag , result_type a, result_type b) {
          return msat_make_xor(env_, a, b ) ;
        }
        
        result_type operator() (predtags::implies_tag , result_type a, result_type b) {
          return msat_make_implies(env_, a, b ) ;
        }

        result_type operator() (predtags::or_tag , result_type a, result_type b) {
          return msat_make_or(env_, a, b ) ;
        }

        result_type operator() (bvtags::var_tag const & var, boost::any args )
        {
          char buf[1024];
          sprintf(buf, "var%d", var.id);
          
          msat_decl decl = msat_declare_variable( env_, buf, MSAT_BV+var.width);
          return msat_make_variable(env_, decl);
        }

        result_type operator() (bvtags::bit0_tag , boost::any arg ) {
          return msat_make_number(env_, "0d1_0");
        }

        result_type operator() (bvtags::bit1_tag , boost::any arg ) {
          return msat_make_number(env_, "0d1_1");
        }
        result_type operator() (bvtags::bvhex_tag , boost::any arg ) {
          std::string hex = boost::any_cast<std::string>(arg);
          char buf[4096];
          sprintf(buf, "0h%u_%s", (unsigned)hex.size()*4, hex.c_str());
          return msat_make_number(env_, buf);
        }

        result_type operator() (bvtags::bvbin_tag , boost::any arg ) {
          std::string bin = boost::any_cast<std::string>(arg);
          char buf[4096];
          sprintf(buf, "0b%u_%s", (unsigned)bin.size(), bin.c_str());
          return msat_make_number(env_, buf);
        }
        result_type operator() (bvtags::bvuint_tag , boost::any arg ) {
          typedef boost::tuple<unsigned long, unsigned long> P;
          P p = boost::any_cast<P>(arg);
          //std::cout << "bvuint "<< p << std::endl;
          unsigned value = boost::get<0>(p);
          unsigned width = boost::get<1>(p);
          char buf[4096];
          sprintf(buf, "0d%u_%u", width, value);
          return msat_make_number(env_, buf);
        }


        //result_type operator() (bvtags::bvsint_tag , boost::any arg ) {
        //  typedef boost::tuple<long, unsigned long> P;
        //  P p = boost::any_cast<P>(arg);
        //  return boolector_int(_btor, boost::get<0>(p), boost::get<1>(p));
        //}

        result_type operator() (bvtags::bvnot_tag , result_type a ) {
          return msat_make_bv_not(env_, a);
        }

        result_type operator() (bvtags::bvneg_tag , result_type a ) {
          return msat_make_bv_neg(env_, a);
        }

        ////////////////////////
        // Fallback operators //
        ////////////////////////

        template <typename TagT>
        result_type operator() (TagT tag, boost::any args ) {
          return msat_make_false(env_);
        }


        template <typename TagT>
        result_type operator() (TagT tag, result_type a ) {
          return msat_make_false(env_);
        }

        template< result_type (*FN) (msat_env, result_type, result_type) > 
        struct F2 {
          static result_type exec(msat_env e , result_type x, result_type y) 
          { return (*FN)(e,x,y);}
        };

        result_type operator() (bvtags::bvnor_tag , result_type a, result_type b) {
          return msat_make_bv_not(env_, msat_make_bv_or(env_,a,b));
        }

        result_type operator() (bvtags::bvnand_tag , result_type a, result_type b) {
          return msat_make_bv_not(env_, msat_make_bv_and(env_,a,b));
        }

        result_type operator() (bvtags::bvxnor_tag , result_type a, result_type b) {
          return msat_make_bv_not(env_, msat_make_bv_xor(env_,a,b));
        }

        result_type operator() (bvtags::bvcomp_tag , result_type a, result_type b) {
          return msat_make_ite(env_, 
              msat_make_equal(env_,a,b)
            , msat_make_number(env_, "0b1_1")
            , msat_make_number(env_, "0b1_0")
          );
        }

        template <typename TagT>
        result_type operator() (TagT tag, result_type a, result_type b) {
          using namespace boost::mpl;

          typedef map<
            pair<bvtags::bvand_tag,     F2<&msat_make_bv_and> >
          , pair<bvtags::bvor_tag,      F2<&msat_make_bv_or > >
          , pair<bvtags::bvxor_tag,     F2<&msat_make_bv_xor> >
          , pair<bvtags::bvadd_tag,     F2<&msat_make_bv_plus> >
          , pair<bvtags::bvsub_tag,     F2<&msat_make_bv_minus> >
          , pair<bvtags::bvmul_tag,     F2<&msat_make_bv_times> >
          , pair<bvtags::bvslt_tag,     F2<&msat_make_bv_slt> >
          > Opcode_Map;

          typedef 
            typename has_key< Opcode_Map, TagT >::type
          _has_key;

          if (_has_key::value ) {
          typedef typename eval_if<
            _has_key
            , at< Opcode_Map, TagT >
            , identity< F2<msat_make_and> >
            >::type opcode;
          return opcode::exec(env_, a, b);
          } else {
            std::cout << "unknown operator: " << tag << std::endl;

            assert(false && "unknown operator");
            return msat_make_false(env_);
          }
        }


        template <typename TagT>
        result_type operator() (TagT tag, result_type a, result_type b, result_type c) {
          return msat_make_false(env_);
        }

      private:
        msat_env env_;
        msat_term assumptions_;
    };
	
  } // namespace solver
} // namespace metaSMT

//  vim: ft=cpp:ts=2:sw=2:expandtab
