#pragma once

#include "tags/QF_BV.hpp"
#include "result_wrapper.hpp"

#include <boost/mpl/vector.hpp>
#include <boost/proto/core.hpp>
#include <boost/variant.hpp>
#include <boost/any.hpp>
#include <boost/foreach.hpp>

#include <iostream>

namespace metaSMT {
  namespace proto = boost::proto;
  namespace bvtags = ::metaSMT::logic::QF_BV::tag;
  namespace predtags = ::metaSMT::logic::tag;

  // Forward declaration
  struct addclause_cmd;
  namespace features
  {
    struct addclause_api;
  }

  template <typename PredicateSolver>
  struct BitBlast {
    typedef BitBlast<PredicateSolver> this_type;

    typedef typename PredicateSolver::result_type result_base;
    typedef std::vector< result_base >  bv_result;

    typedef typename boost::mpl::vector2<
      result_base, bv_result
    >::type result_types_vec;

    typedef typename boost::make_variant_over< result_types_vec >::type 
      result_type;
      
    
        void assertion( result_type e ) { 
          _solver.assertion( boost::get<result_base>(e) );
        }

        void assumption( result_type e ) { 
          _solver.assumption( boost::get<result_base>(e) );
        }
        
        bool solve() {
          return _solver.solve();
        }

        result_type operator() (bvtags::var_tag var, boost::any arg ) {
          //printf("bitvec\n");
          bv_result ret(var.width);
          for (unsigned i = 0; i < var.width; ++i) {
            ret[i]= _solver(predtags::var_tag(), arg);
          }
          return ret;
        }

        result_type operator() ( bvtags::bvand_tag , result_type arg1, result_type arg2 ) 
        {
          //printf("bvand\n");
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          bv_result ret(a.size());
          predtags::and_tag and_;

          for (unsigned i = 0; i < a.size(); ++i) {
            ret[i]= _solver(and_, a[i], b[i]);
          }
          return ret;
        }
        
        
        result_type operator() ( bvtags::bvnand_tag , result_type arg1, result_type arg2 ) 
        {
          //printf("bvnand\n");
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          bv_result ret(a.size());
          predtags::nand_tag nand_;

          for (unsigned i = 0; i < a.size(); ++i) {
            ret[i]= _solver(nand_, a[i], b[i]);
          }
          return ret;
        }
        
        result_type operator() ( bvtags::bvor_tag , result_type arg1, result_type arg2 ) 
        {
          //printf("bvor\n");
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          bv_result ret(a.size());
          predtags::or_tag or_;

          for (unsigned i = 0; i < a.size(); ++i) {
            ret[i]= _solver(or_, a[i], b[i]);
          }
          return ret;
        }
      
        result_type operator() ( bvtags::bvnor_tag , result_type arg1, result_type arg2 ) 
        {
          //printf("bvnor\n");
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          bv_result ret(a.size());
          predtags::nor_tag tag_;

          for (unsigned i = 0; i < a.size(); ++i) {
            ret[i]= _solver(tag_, a[i], b[i]);
          }
          return ret;
        }
           
        result_type operator() ( bvtags::bvnot_tag , result_type arg1 ) 
        {
         //printf("bvnot\n");
          bv_result a = boost::get<bv_result>(arg1);
          bv_result ret(a.size());
          predtags::not_tag not_;
          
          for (unsigned i = 0; i < a.size(); ++i) {
            ret[i] = _solver(not_,a[i]);
          }
          return ret;
        }
       
       
       result_type operator() ( bvtags::bvxor_tag , result_type arg1, result_type arg2 ) 
       {
          //printf("bvxor\n");
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          bv_result ret(a.size());
          predtags::xor_tag xor_;

          for (unsigned i = 0; i < a.size(); ++i) {
            ret[i]= _solver(xor_, a[i], b[i]);
          }
          return ret;
       }
       
       result_type operator() ( bvtags::bvxnor_tag , result_type arg1, result_type arg2 ) 
       {
          //printf("bvxnor\n");
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          bv_result ret(a.size());
          predtags::xnor_tag xnor_;

          for (unsigned i = 0; i < a.size(); ++i) {
            ret[i]= _solver(xnor_, a[i], b[i]);
          }
          return ret;
        }
      
      
       result_type operator() (bvtags::bvult_tag, result_type arg1, result_type arg2)
       {
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          assert(a.size()>0);
          
          typename bv_result::reverse_iterator ai, bi, end;
          ai = a.rbegin();
          bi = b.rbegin();
          end= a.rend();
                  
          
          result_base not_a = _solver(predtags::not_tag(), *ai);
          result_base ret = _solver(predtags::and_tag(),not_a, *bi);  
          result_base equal = _solver(predtags::xnor_tag(), *ai, *bi);
         

          for (++ai, ++bi ; ai != end; ++ai, ++bi) 
          {
            not_a = _solver(predtags::not_tag(), *ai);
            result_base now_less = _solver(predtags::and_tag(),not_a, *bi);
            result_base now   = _solver(predtags::and_tag(), equal, now_less);
            
            result_base now_equal = _solver(predtags::xnor_tag(), *ai, *bi);
            equal = _solver(predtags::and_tag(), now_equal, equal);

            ret = _solver(predtags::or_tag(), ret, now);
          }
          return ret;
       }
       
       result_type operator() (bvtags::bvugt_tag, result_type arg1, result_type arg2)
       {
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          assert(a.size()>0);
          
          typename bv_result::reverse_iterator ai, bi, end;
          ai = a.rbegin();
          bi = b.rbegin();
          end= a.rend();
                  
          
          result_base not_b = _solver(predtags::not_tag(), *bi);
          result_base ret = _solver(predtags::and_tag(), *ai, not_b);  
          result_base equal = _solver(predtags::xnor_tag(), *ai, *bi);
         

          for (++ai, ++bi ; ai != end; ++ai, ++bi) 
          {
            not_b = _solver(predtags::not_tag(), *bi);
            result_base now_great = _solver(predtags::and_tag(),*ai, not_b);
            result_base now   = _solver(predtags::and_tag(), equal, now_great);
            
            result_base now_equal = _solver(predtags::xnor_tag(), *ai, *bi);
            equal = _solver(predtags::and_tag(), now_equal, equal);

            ret = _solver(predtags::or_tag(), ret, now);
          }
          return ret;
       }
       
       result_type operator() (bvtags::bvsgt_tag, result_type arg1, result_type arg2)
       {
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          assert(a.size()>0);
          
          typename bv_result::reverse_iterator ai, bi, end;
          ai = a.rbegin();
          bi = b.rbegin();
          end= a.rend();
                  
          result_base not_a = _solver(predtags::not_tag(), *ai);
          result_base not_b = _solver(predtags::not_tag(), *bi);
          result_base ret = _solver(predtags::and_tag(), not_a, *bi);  
          result_base equal = _solver(predtags::xnor_tag(), *ai, *bi);
         

          for (++ai, ++bi ; ai != end; ++ai, ++bi) 
          {
            not_b = _solver(predtags::not_tag(), *bi);
            
            result_base now_great = _solver(predtags::and_tag(),*ai, not_b);
            result_base now   = _solver(predtags::and_tag(), equal, now_great);
            
            result_base now_equal = _solver(predtags::xnor_tag(), *ai, *bi);
            equal = _solver(predtags::and_tag(), now_equal, equal);

            ret = _solver(predtags::or_tag(), ret, now);
          }
          return ret;
       }
       

        result_type operator() (bvtags::bvslt_tag, result_type arg1, result_type arg2)
       {
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          assert(a.size()>0);
          
          typename bv_result::reverse_iterator ai, bi, end;
          ai = a.rbegin();
          bi = b.rbegin();
          end= a.rend();
                  
          result_base not_a = _solver(predtags::not_tag(), *ai);
          result_base not_b = _solver(predtags::not_tag(), *bi);
          result_base ret = _solver(predtags::and_tag(), *ai, not_b);  
          result_base equal = _solver(predtags::xnor_tag(), *ai, *bi);
         

          for (++ai, ++bi ; ai != end; ++ai, ++bi) 
          {
            not_a = _solver(predtags::not_tag(), *ai);
            result_base now_less = _solver(predtags::and_tag(),not_a, *bi);
            result_base now   = _solver(predtags::and_tag(), equal, now_less);
            
            result_base now_equal = _solver(predtags::xnor_tag(), *ai, *bi);
            equal = _solver(predtags::and_tag(), now_equal, equal);

            ret = _solver(predtags::or_tag(), ret, now);
          }
          return ret;
       }
       
       
        result_type operator() (bvtags::bvule_tag, result_type arg1, result_type arg2)
        {
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          assert(a.size()>0);
          
          typename bv_result::reverse_iterator ai, bi, end;
          ai = a.rbegin();
          bi = b.rbegin();
          end= a.rend();
                  
          result_base not_a = _solver(predtags::not_tag(), *ai);
        //  result_base not_b = _solver(predtags::not_tag(), *bi);
          result_base less = _solver(predtags::and_tag(), not_a, *bi);  
          result_base equal = _solver(predtags::xnor_tag(), *ai, *bi);
          result_base ret = less; 
          
          

          for (++ai, ++bi ; ai != end; ++ai, ++bi) 
          {
            not_a = _solver(predtags::not_tag(), *ai);
            result_base now_less = _solver(predtags::and_tag(),not_a, *bi);
            result_base now   = _solver(predtags::and_tag(), equal, now_less);
            
            result_base now_equal = _solver(predtags::xnor_tag(), *ai, *bi);
            equal = _solver(predtags::and_tag(), now_equal, equal);

            ret = _solver(predtags::or_tag(), ret, now);
          }
          ret = _solver(predtags::or_tag(), ret, equal);
          return ret;
        }
        
        


        result_type operator() (bvtags::bvuge_tag, result_type arg1, result_type arg2)
        {
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          assert(a.size()>0);
          
          typename bv_result::reverse_iterator ai, bi, end;
          ai = a.rbegin();
          bi = b.rbegin();
          end= a.rend();
                  
          result_base not_b = _solver(predtags::not_tag(), *bi);
        //  result_base not_b = _solver(predtags::not_tag(), *bi);
          result_base great = _solver(predtags::and_tag(), *ai, not_b);  
          result_base equal = _solver(predtags::xnor_tag(), *ai, *bi);
          result_base ret = great;


          for (++ai, ++bi ; ai != end; ++ai, ++bi) 
          {
            not_b = _solver(predtags::not_tag(), *bi);
            result_base now_great = _solver(predtags::and_tag(),*ai, not_b);
            result_base now   = _solver(predtags::and_tag(), equal, now_great);
            
            result_base now_equal = _solver(predtags::xnor_tag(), *ai, *bi);
            equal = _solver(predtags::and_tag(), now_equal, equal);

            ret = _solver(predtags::or_tag(), ret, now);
          }
          ret = _solver(predtags::or_tag(), ret, equal);
          return ret;
        }
       
       result_type operator() (bvtags::bvsge_tag, result_type arg1, result_type arg2)
       {
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          assert(a.size()>0);
          
          typename bv_result::reverse_iterator ai, bi, end;
          ai = a.rbegin();
          bi = b.rbegin();
          end= a.rend();
                  
          result_base not_a = _solver(predtags::not_tag(), *ai);
          result_base not_b = _solver(predtags::not_tag(), *bi);
          result_base great = _solver(predtags::and_tag(), not_a, *bi);  
          result_base equal = _solver(predtags::xnor_tag(), *ai, *bi);
          result_base ret = great;

          for (++ai, ++bi ; ai != end; ++ai, ++bi) 
          {
            not_b = _solver(predtags::not_tag(), *bi);
            result_base now_great = _solver(predtags::and_tag(),*ai, not_b);
            result_base now   = _solver(predtags::and_tag(), equal, now_great);
            
            result_base now_equal = _solver(predtags::xnor_tag(), *ai, *bi);
            equal = _solver(predtags::and_tag(), now_equal, equal);

            ret = _solver(predtags::or_tag(), ret, now);
          }
          ret = _solver(predtags::or_tag(), ret, equal);
          return ret;
       }
       

        result_type operator() (bvtags::bvsle_tag, result_type arg1, result_type arg2)
       {
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          assert(a.size()>0);
          
          typename bv_result::reverse_iterator ai, bi, end;
          ai = a.rbegin();
          bi = b.rbegin();
          end= a.rend();
                  
          result_base not_b = _solver(predtags::not_tag(), *bi);
          result_base less = _solver(predtags::and_tag(), *ai, not_b);  
          result_base equal = _solver(predtags::xnor_tag(), *ai, *bi);
          result_base ret = less;

          for (++ai, ++bi ; ai != end; ++ai, ++bi) 
          {
            result_base not_a = _solver(predtags::not_tag(), *ai);
            result_base now_less = _solver(predtags::and_tag(),not_a, *bi);
            result_base now   = _solver(predtags::and_tag(), equal, now_less);
            
            result_base now_equal = _solver(predtags::xnor_tag(), *ai, *bi);
            equal = _solver(predtags::and_tag(), now_equal, equal);

            ret = _solver(predtags::or_tag(), ret, now);
          }
          ret = _solver(predtags::or_tag(), ret, equal);
          return ret;
       }
       
        result_type operator() (bvtags::bvadd_tag, result_type arg1, result_type arg2)
       {
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          assert(a.size()==b.size());
          
          bv_result ret(a.size());
          
          result_base carry = _solver(predtags::false_tag(), boost::any());
          
          result_base xor1, or1, and1, and2;
         
          for (unsigned i = 0; i < a.size(); ++i) {
              
              xor1 = _solver(predtags::xor_tag(), a[i], b[i]);
              ret[i] = _solver(predtags::xor_tag(), xor1, carry);
              
              // a&b | c&(a|b) 
              and1 = _solver(predtags::and_tag(), a[i], b[i]);
              or1  = _solver(predtags::or_tag(),a[i],b[i]);
              and2 = _solver(predtags::and_tag(),carry, or1);
              carry  = _solver(predtags::or_tag(), and1, and2);
                          
            }
          return ret;
       }

       result_type operator() (bvtags::bvmul_tag, result_type arg1, result_type arg2)
       {
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
          result_type ret = bv_result (a.size(), _solver( predtags::false_tag(), boost::any() ) );
          result_type tmp1;
          
          for(unsigned i = 0 ; i < a.size() ; ++i)
          {
            tmp1 = (*this)(bvtags::sign_extend_tag(),a.size()-1,bv_result(1,a[i]));
            tmp1 = (*this)(bvtags::bvand_tag(),arg2,tmp1);
            tmp1 = shiftL( boost::get<bv_result>(tmp1),i);
            
            ret = (*this)(bvtags::bvadd_tag(),ret,tmp1);
          }
          return ret;
       }
     
       result_type operator() ( bvtags::bvneg_tag, result_type arg1 )
       {
       
          bv_result a = boost::get<bv_result>(arg1);
          
          bv_result tmp1(a.size(),_solver(predtags::false_tag(),boost::any()));
          tmp1.front()= _solver(predtags::true_tag(), boost::any());
          result_type tmp2 = (*this)(bvtags::bvnot_tag(), arg1);
          
          return (*this)(bvtags::bvadd_tag(),tmp2,tmp1);
       }
       
       result_type operator() ( bvtags::bvudiv_tag, result_type arg1, result_type arg2 )
       {
            return uDivRem(arg1,arg2,true);
       }
   
       result_type operator() ( bvtags::bvsdiv_tag, result_type arg1, result_type arg2 )
       {
        return sDivRem(arg1,arg2,true); 
       }

       result_type operator() ( bvtags::bvsrem_tag, result_type arg1, result_type arg2 )
       {
        return sDivRem(arg1,arg2,false); 
       }
     
     result_type operator() ( bvtags::bvhex_tag , boost::any arg )
       {
               std::string str = boost::any_cast<std::string>(arg);
               result_base _0 = _solver(predtags::false_tag(),boost::any());               
               result_base _1 = _solver(predtags::true_tag(),boost::any());               
               bv_result ret(str.size()*4,_0);
               typename bv_result::iterator iter = ret.begin();
          
          BOOST_REVERSE_FOREACH( const char c, str) {
            switch ( c ) {
              case '0':
                *(iter++) = _0;
                *(iter++) = _0;
                *(iter++) = _0;
                *(iter++) = _0;                
               break;
              case '1':
                *(iter++) = _1;
                *(iter++) = _0;
                *(iter++) = _0;
                *(iter++) = _0;                
               break;
              case '2':
                *(iter++) = _0;
                *(iter++) = _1;
                *(iter++) = _0;
                *(iter++) = _0;              
               break;
              case '3':
                *(iter++) = _1;
                *(iter++) = _1;
                *(iter++) = _0;
                *(iter++) = _0;                
               break;
              case '4':
                *(iter++) = _0;
                *(iter++) = _0;
                *(iter++) = _1;
                *(iter++) = _0;                
               break;
              case '5':
                *(iter++) = _1;
                *(iter++) = _0;
                *(iter++) = _1;
                *(iter++) = _0;                
               break;
              case '6':
                *(iter++) = _0;
                *(iter++) = _1;
                *(iter++) = _1;
                *(iter++) = _0;                
               break;
              case '7':
                *(iter++) = _1;
                *(iter++) = _1;
                *(iter++) = _1;
                *(iter++) = _0;                
               break;
              case '8':
                *(iter++) = _0;
                *(iter++) = _0;
                *(iter++) = _0;
                *(iter++) = _1;                
               break;
              case '9':
                *(iter++) = _1;
                *(iter++) = _0;
                *(iter++) = _0;
                *(iter++) = _1;                
               break;
              case 'a':
              case 'A':
                *(iter++) = _0;
                *(iter++) = _1;
                *(iter++) = _0;
                *(iter++) = _1;                
               break;
              case 'b':
              case 'B':
                *(iter++) = _1;
                *(iter++) = _1;
                *(iter++) = _0;
                *(iter++) = _1;                
               break;
              case 'c':
              case 'C':
                *(iter++) = _0;
                *(iter++) = _0;
                *(iter++) = _1;
                *(iter++) = _1;                
               break;
              case 'd':
              case 'D':
                *(iter++) = _1;
                *(iter++) = _0;
                *(iter++) = _1;
                *(iter++) = _1;                
               break;
              case 'e':
              case 'E':
                *(iter++) = _0;
                *(iter++) = _1;
                *(iter++) = _1;
                *(iter++) = _1;                
               break;
              case 'f':
              case 'F':
                *(iter++) = _1;
                *(iter++) = _1;
                *(iter++) = _1;
                *(iter++) = _1;                  
               break;                        
             }   
          }
          
          return ret;
          
       }
      
       result_type operator() ( bvtags::bvurem_tag, result_type arg1, result_type arg2 )
       {
            return uDivRem(arg1,arg2, false);
       }
            
       result_type operator() ( bvtags::bvsub_tag, result_type arg1, result_type arg2 )
       {
          result_type tmp ((*this)(bvtags::bvneg_tag(), arg2));
                          
           return (*this)(bvtags::bvadd_tag(), arg1,tmp);
       }

     result_type operator() ( bvtags::bvcomp_tag, result_type arg1, result_type arg2 )
       {
          result_type tmp = (*this)(predtags::equal_tag(), arg1,arg2);
          
          result_base ret = boost::get<result_base>(tmp);
                     
          return bv_result(1,ret);
       }

       result_type operator() ( bvtags::zero_extend_tag, unsigned width, result_type arg1 ) 
       {
          bv_result a = boost::get<bv_result>(arg1);
          bv_result tmp(a.size()+width,_solver(predtags::false_tag(),boost::any()));
          
          std::copy(a.begin(), a.end(), tmp.begin());
          return tmp;
       }
       
       result_type operator() ( bvtags::sign_extend_tag, unsigned width, result_type arg1 ) 
       {
          bv_result a = boost::get<bv_result>(arg1);
          assert(!a.empty());
          bv_result tmp(a.size()+width, a.back());
          
          std::copy(a.begin(), a.end(), tmp.begin());
          return tmp;
       }
       

       result_type operator() ( predtags::equal_tag eq, result_type arg1, result_type arg2 ) 
       {
          result_base ret;
          //printf("try to compare bv\n");
          try {
            //printf("read arg1\n");
            bv_result a = boost::get<bv_result>(arg1);
            //printf("read arg2\n");
            bv_result b = boost::get<bv_result>(arg2);
            assert(a.size()==b.size());
            ret = _solver(predtags::true_tag(), boost::any());
            for (unsigned i = 0; i < a.size(); ++i) {
              result_base cur = _solver(eq, a[i], b[i]);
              ret = _solver(predtags::and_tag(), cur, ret);
            }
          } catch (boost::bad_get) {
            //printf("try to compare bool\n");
            //printf("read arg1\n");
            result_base a = boost::get<result_base>(arg1);
            //printf("read arg2\n");
            result_base b = boost::get<result_base>(arg2);
            ret = _solver(eq, a, b);
          }
          //printf("compare done\n");
          return ret;
       }

       result_type operator() ( predtags::nequal_tag neq, result_type arg1, result_type arg2 ) 
       {
          result_base ret;
          //printf("try to compare bv\n");
          try {
            //printf("read arg1\n");
            bv_result a = boost::get<bv_result>(arg1);
            //printf("read arg2\n");
            bv_result b = boost::get<bv_result>(arg2);
            assert(a.size()==b.size());
            ret = _solver(predtags::false_tag(), boost::any());
            for (unsigned i = 0; i < a.size(); ++i) {
              result_base cur = _solver(neq, a[i], b[i]);
              ret = _solver(predtags::or_tag(), cur, ret);
            }
          } catch (boost::bad_get) {
            //printf("try to compare bool\n");
            //printf("read arg1\n");
            result_base a = boost::get<result_base>(arg1);
            //printf("read arg2\n");
            result_base b = boost::get<result_base>(arg2);
            ret = _solver(neq, a, b);
          }
          //printf("compare done\n");
          return ret;
       }

        
        result_type operator() (bvtags::bvbin_tag , boost::any arg ) {
          //printf("bvbin\n");
          std::string value = boost::any_cast<std::string>(arg);
          bv_result ret (value.size());
          result_base one  = _solver(predtags::true_tag (), boost::any());
          result_base zero = _solver(predtags::false_tag(), boost::any());
          std::string::reverse_iterator vite = value.rbegin();
          typename bv_result::iterator rite = ret.begin();
          for (unsigned i = 0; i < value.size(); ++i) {
            *rite = (*vite)=='1' ? one : zero;
            ++rite;
            ++vite;
          }
          return ret;
        }
        
        result_type operator() (bvtags::bvuint_tag , boost::any arg ) {
          typedef boost::tuple<unsigned long, unsigned long> P;
          P p = boost::any_cast<P>(arg);
          //std::cout << "bvuint "<< p << std::endl;
          unsigned long value = boost::get<0>(p);
          unsigned long width = boost::get<1>(p);
        
          bv_result ret (width);
          result_base one  = _solver(predtags::true_tag (), boost::any());
          result_base zero = _solver(predtags::false_tag(), boost::any());
          for (unsigned long i = 0; i < width; ++i) {
            ret[i] = (value & 1) ? one : zero;
            value >>=1;
          }
          return ret;
        }

        result_type operator() (bvtags::bvsint_tag , boost::any arg ) {
          typedef boost::tuple< long, unsigned long> P;
          P p = boost::any_cast<P>(arg);
          signed long value = boost::get<0>(p);
          unsigned long width = boost::get<1>(p);
        
          bv_result ret (width);
          result_base one  = _solver(predtags::true_tag (), boost::any());
          result_base zero = _solver(predtags::false_tag(), boost::any());
          for (unsigned long i = 0; i < width; ++i) {
            ret[i] = (value & (1l << i )) ? one : zero;
          }
          return ret;
        }
       
        
        result_type operator() (bvtags::bit0_tag , boost::any arg ) {
          //printf("bit0\n");
          return bv_result(1,_solver(predtags::false_tag(), arg));
        }

        result_type operator() (bvtags::bit1_tag , boost::any arg ) {
          //printf("bit1\n");
          return bv_result(1,_solver(predtags::true_tag(), arg));
        }

        result_type operator() (bvtags::bvshr_tag, result_type arg1, result_type value) {
          bv_result a = boost::get<bv_result>(arg1);
          
          result_base zero = _solver(predtags::false_tag(),boost::any());
          result_type ret = bv_result(a.size(), zero);
          predtags:: ite_tag ite;
          
          for(unsigned i = 0; i < a.size(); ++i)
          {
            result_type index = (*this)(bvtags::bvuint_tag()
                ,boost::any(boost::tuple<unsigned long, unsigned long>(i,a.size())));
            ret = (*this)(ite, 
                (*this)(predtags::equal_tag(), value, index)
              , shiftR(a, i, zero)
              , ret
            );
          }
         
          return ret; 
        }
      
        result_type operator() (bvtags::bvshl_tag, result_type arg1, result_type value ) {
          
          bv_result a = boost::get<bv_result>(arg1);
          
          result_type ret = bv_result(a.size(), _solver(predtags::false_tag(), boost::any()));
          predtags:: ite_tag ite;
          
          for(unsigned i = 0; i < a.size(); ++i)
          {
            result_type index = (*this)(bvtags::bvuint_tag()
                ,boost::any(boost::tuple<unsigned long, unsigned long>(i,a.size())));
            ret = (*this)(ite, 
                (*this)(predtags::equal_tag(), value, index)
              , shiftL(a, i)
              , ret
            );
          }
          return ret;         
        }
        
        result_type operator() (bvtags::bvashr_tag, result_type arg1, result_type value ) {
        bv_result a = boost::get<bv_result>(arg1);
          
 
          result_type ret = bv_result(a.size(), a.back());
          predtags:: ite_tag ite;
          
          for(unsigned i = 0; i < a.size(); ++i)
          {
            result_type index = (*this)(bvtags::bvuint_tag()
                ,boost::any(boost::tuple<unsigned long, unsigned long>(i,a.size())));
            ret = (*this)(ite, 
                (*this)(predtags::equal_tag(), value, index)
              , shiftR(a, i, a.back())
              , ret
            );
          }
         
          return ret; 
        }
        
        
        result_type operator() (predtags::ite_tag, result_type arg1, result_type arg2, result_type arg3 ) {
                 
          result_base c = boost::get<result_base>(arg1);
          predtags::ite_tag ite;
          
          try {
           bv_result a = boost::get<bv_result>(arg2);
           bv_result b = boost::get<bv_result>(arg3);
           bv_result ret(a.size());
           assert(a.size()==b.size());
          
           for (unsigned i = 0; i < a.size(); ++i) {
               ret[i]= _solver(ite,c,a[i],b[i]);
           }
          
           return ret;
          } 
           catch (boost::bad_get) {
           result_base a = boost::get<result_base>(arg2);
           result_base b = boost::get<result_base>(arg3);
            return _solver(ite,c,a,b); 
          }
          
         
        }

        struct bv_getter : public boost::static_visitor<bv_result> {
          bv_result operator() (bv_result const & bv) const {
            return bv;
          }
          template <typename T>
          bv_result operator() (T) const {
            assert(false && "expected bitvector here.");
            return bv_result();
          }
        };

        result_type operator() (bvtags::extract_tag const & 
            , unsigned long upper, unsigned long lower
            , result_type e
        ) {
          bv_result ret(upper-lower+1);
          bv_result bv = boost::apply_visitor(bv_getter(), e);
          std::copy(bv.begin()+lower, bv.begin()+upper+1, ret.begin());
          return ret;
        }

        result_type operator() (bvtags::concat_tag const & 
            , result_type e1, result_type e2
        ) {
          bv_result bv1 = boost::apply_visitor(bv_getter(), e1);
          bv_result bv2 = boost::apply_visitor(bv_getter(), e2);
          bv_result ret(bv1.size()+bv2.size());
          typename bv_result::iterator iter = ret.begin();
          std::copy(bv2.begin(), bv2.end(), ret.begin() );
          std::copy(bv1.begin(), bv1.end(), ret.begin() + bv2.size() );
          return ret;
        }

        result_wrapper read_value(result_type var)
        { 
          try {
            return read_value(boost::get<result_base>(var)); 
          } catch ( boost::bad_get ) {
            return read_value(boost::get<bv_result>(var)); 
          }
        }

        result_wrapper read_value(result_base var)
        { 
          return _solver.read_value(var); 
        }

        result_wrapper read_value(bv_result const & vars)
        { 
          std::vector<boost::logic::tribool> ret(vars.size());
          std::vector<boost::logic::tribool>::iterator it
            = ret.begin();

          for (unsigned i = 0; i < vars.size(); ++i, ++it) {
            *it = _solver.read_value( vars[i] );
          }
      
          return result_wrapper(ret);
        }

        ////////////////////////
        // Fallback operators //
        ////////////////////////

        template <typename TagT, typename Any>
        //boost::disable_if< boost::is_same(Any, bv_result)::type, result_type >::type
        result_type 
        operator() (TagT tag, Any args ) {
          try {
            // std::cout << "operator " << tag << std::endl;
           return _solver(tag, args);
          } catch (boost::bad_get) {
            std::cout << "Error bad_get in operator " << tag << std::endl;
            throw;
          }
        }

        template <typename TagT>
        result_type operator() (TagT tag, result_type a ) {
          return _solver( tag
            , boost::get<result_base>(a)
          );
        }

        template <typename TagT>
        result_type operator() (TagT tag, result_type a, result_type b) {
          try {
          return _solver( tag
            , boost::get<result_base>(a)
            , boost::get<result_base>(b)
          );
          } catch (boost::bad_get) {
            std::cout << "Error bad_get in operator " << tag << std::endl;
            throw;
          }
        }

        template <typename TagT>
        result_type operator() (TagT tag, result_type a, result_type b, result_type c) {
          try {
          return _solver( tag
            , boost::get<result_base>(a)
            , boost::get<result_base>(b)
            , boost::get<result_base>(c)
          );
          } catch (boost::bad_get) {
            std::cout << "Error bad_get in operator " << tag << std::endl;
            throw;
          }
        }

      /* pseudo command */
      void command ( BitBlast<PredicateSolver> const & ) { };
      template<typename Command, typename Expr>
      void command ( Command const& cmd, Expr& expr )
      {
        _solver.command ( cmd, expr );
      }


    private:
      result_type sDivRem (result_type arg1, result_type arg2, bool value) {
  
        bv_result a = boost::get<bv_result>(arg1);       
        bv_result b = boost::get<bv_result>(arg2);
         
        predtags:: ite_tag ite;
        predtags:: xor_tag xor_;
        bvtags:: bvneg_tag neg;
        
        result_type tmp1 = (*this)(neg,arg1);
        result_type tmp2 = (*this)(neg,arg2);
   
      
        result_type aneg = (*this)(ite, a.back(), (*this)(neg,arg1),arg1);
        result_type bneg = (*this)(ite, b.back(), (*this)(neg,arg2),arg2);
          
             
        result_type test = uDivRem(aneg,bneg,value);
            
        test = (*this)(ite, _solver(xor_, a.back(), b.back()), (*this)(neg,test),test);
        
        return test;        
      }  
      
    private: 
      result_type uDivRem (result_type arg1, result_type arg2, bool value) {
        
          bv_result a = boost::get<bv_result>(arg1);
          bv_result b = boost::get<bv_result>(arg2);
        
          result_type divisor = arg2 ;

          result_base zero = _solver(predtags::false_tag(), boost::any());
          result_base one = _solver(predtags::true_tag(), boost::any());
          
          bv_result ret(a.size(),zero);
          result_type checker = zero; 
          predtags::ite_tag ite;
         /*
         
          bvtags:: bvand_tag and_;
          bvtags:: bvneg_tag neg;
                   
        result_type ret1 = (*this)(bvtags::bvuge_tag(), a, ret);
        result_type ret2 = (*this)(bvtags::bvuge_tag(), b, ret); 
        result_type ret3 = (*this)(bvtags::bvslt_tag(), a, ret);
        result_type ret4 = (*this)(bvtags::bvslt_tag(), b, ret);
                
       result_type bneg = (*this)(ite, _solver(and_, ret1, ret4), (*this)(bvtags::bvneg_tag(),arg2),b);
       b = boost::get<bv_result>(bneg);
       
       result_type aneg = (*this)(ite, _solver(and_, ret3, ret2), (*this)(bvtags::bvneg_tag(),arg1),a);
       a = boost::get<bv_result>(aneg);
        
        result_type aeg = (*this)(ite, _solver(and_, ret3, ret4), (*this)(bvtags::bvneg_tag(),arg1),a);
        a = boost::get<bv_result>(aeg);
        
        result_type args1 = a;
        result_type args2 = b; 
        */  
           for(unsigned i = 0; i < a.size(); ++i)
          {
             result_type tmp = b.back();
             divisor = (*this)(ite,tmp, divisor, shiftL(b,1));
             b = boost::get<bv_result>(divisor);
          }
          
          for(unsigned i = 1; i <=a.size(); ++i)
          {
            result_type bef_dev = divisor;
            result_type do_devide = (*this)(bvtags::bvuge_tag(), arg1, divisor);
            result_type eq = (*this)(predtags::equal_tag(),bef_dev,arg2);    
            
             arg1 = (*this)(ite, do_devide, (*this)(bvtags::bvsub_tag(), arg1, divisor),arg1);
       
        
            divisor = (*this)(ite, eq, divisor, shiftR(boost::get<bv_result>(divisor), 1, zero));    
             
             do_devide = (*this)(ite,checker,zero, do_devide);      
             ret[a.size()-i] = boost::get<result_base>(do_devide);
        
             result_type bo = (*this)(ite,checker,shiftR(ret,1, zero),ret);
             
             ret = boost::get<bv_result>(bo);
             
             
             checker = (*this)(ite, eq , one, checker); 
         } 
                   
          if(value)
          {
            return ret;
          }
        
        return arg1; 
       }
    
    
    
    
    private:
      result_type shiftR (bv_result a, unsigned value, result_base & x) {
                
        //bv_result a = boost::get<bv_result>(arg);
        bv_result ret(a.size());
        
        if(value == 0)
        {
          return a;
        } 
        
        for(unsigned i= 0; i < a.size(); ++value,++i)
        {
          if(value < a.size())
          {
            ret[i] = a[value];
          } else
            ret[i] = x;
        }
       return ret; 
      } 

   private:
      result_type shiftL (bv_result a, unsigned value) {
                
        //bv_result a = boost::get<bv_result>(arg);
        bv_result ret(a.size());
        
        if(value == 0)
        {
          return a;
        } 
        
        for(unsigned i= 0; i < a.size(); ++i)
        {
          if( i < value)
          {
             ret[i] = _solver(predtags::false_tag(),boost::any());
          } else
             ret[i] = a[i-value];
        }
       return ret; 
      } 

    private:
        PredicateSolver _solver;

  };

  namespace features {
    /* Stack supports stack api */
    template<typename Context>
    struct supports< BitBlast<Context>, features::addclause_api>
    : boost::mpl::true_ {};

    /* Forward all other supported operations */
    template<typename Context, typename Feature>
    struct supports< BitBlast<Context>, Feature>
    : supports<Context, Feature>::type {};
  }


} // namespace metaSMT 

//  vim: ft=cpp:ts=2:sw=2:expandtab
