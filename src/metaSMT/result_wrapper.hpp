#pragma once

#include <metaSMT/support/disable_warnings.hpp>
#include <boost/mpl/vector.hpp>
#include <boost/variant.hpp>
#include <boost/concept_check.hpp>
#include <boost/logic/tribool.hpp>
#include <boost/dynamic_bitset.hpp>
#include <boost/type_traits/is_same.hpp>
#include <boost/type_traits/is_signed.hpp>
#include <boost/optional.hpp>
#include <boost/function.hpp>
#include <boost/algorithm/string/case_conv.hpp>
#include <metaSMT/support/enable_warnings.hpp>

#include <vector>

namespace metaSMT {
  /** 
   * return value wrapper
   *
   */ 
  class result_wrapper {

    // converter types
    struct as_vector_tribool 
    {
      typedef std::vector<boost::logic::tribool > result_type;

      result_type operator() ( result_type const & v ) const {
        return v;
      }
      result_type operator() ( boost::logic::tribool const & t ) const {
        result_type ret (1, t);
        return ret;
      }

      result_type operator() (bool b ) const {
        result_type ret (1);
        ret[0]=b;
        return ret;
      }

      result_type operator() ( std::vector<bool> const & vb) const {
        result_type ret (vb.size());
        for (unsigned i = 0; i < vb.size(); ++i) {
          ret[i] = vb[i];
        }
        return ret;
      }

      result_type operator() ( std::string const & s ) const {
        unsigned size = s.size();
        result_type ret(size);
        for (unsigned i = 0; i < size; ++i) {
          switch(s[size-i-1]){
            case '0': 
              ret[i] = false; break;
            case '1': 
              ret[i] = true; break;
            default:
              ret[i] = boost::logic::indeterminate;
          }
        }
        return ret;
      }

      template<typename T, typename T2>
      result_type operator() ( boost::dynamic_bitset<T, T2> const & t ) const {
        result_type ret (t.size());
        for (unsigned i = 0; i < t.size(); ++i) {
          ret[i] = t[i];
        }
        return ret;
      }

    };

    struct as_tribool 
    {
      typedef boost::logic::tribool result_type;

      result_type operator() ( result_type const & v ) const {
        return v;
      }
      result_type operator() ( std::vector<boost::logic::tribool> const & t ) const {
        boost::logic::tribool ret = false;
        for (unsigned i = 0; i < t.size(); ++i) {
          ret = ret||t[i];
        }
        return ret;
      }

      template<typename T, typename T2>
      result_type operator() ( boost::dynamic_bitset<T, T2> const & t ) const {
        for (unsigned i = 0; i < t.size(); ++i) {
          if (t[i]) return true;
        }
        return false;
      }

      result_type operator() (bool b ) const {
        return b;
      }

      result_type operator() ( std::vector<bool> const & vb) const {
        for (unsigned i = 0; i < vb.size(); ++i) {
          if (vb[i]) return true;
        }
        return false;
      }

      result_type operator() ( std::string const & s ) const {
        // true if any bit is true;
        boost::logic::tribool ret = false;
        for (unsigned i = 0; i < s.size(); ++i) {
        switch(s[i]){
          case '0': 
            break;
          case '1': 
            return true;
          default:
            ret = boost::logic::indeterminate;
          }
        }
        return ret;
      }
    };


    struct as_vector_bool
    {
      typedef  std::vector<bool> result_type;

      result_type operator() ( result_type const & v ) const
      { return v; }

      result_type operator() ( boost::logic::tribool t) {
        result_type ret(1);
        ret[0] = t;
        return ret;
      }

      result_type operator() ( bool b ) const {
        result_type ret(1);
        ret[0] = b;
        return ret;
      }

      result_type operator() ( std::vector< boost::logic::tribool > vt ) const {
        result_type ret(vt.size());
        for (unsigned i = 0; i < vt.size(); ++i)
         ret[i] = vt[i];
        return ret;
      }

      result_type operator() ( std::string s) const {
        result_type ret(s.size());
        for (unsigned i = 0; i < s.size(); ++i)
         ret[i] = (s[s.size() - i -1] == '1');
        return ret;
      }

      template<typename T, typename T2>
      result_type operator() ( boost::dynamic_bitset<T, T2> const & t ) const {
        result_type ret (t.size());
        for (unsigned i = 0; i < t.size(); ++i) {
          ret[i] = t[i];
        }
        return ret;
      }
    };

    struct as_string
    {
      typedef std::string result_type; 

      result_type operator() ( result_type const & v ) const {
        return v;
      }

      result_type operator() ( bool b ) const {
        return b ? "1" : "0";
      }

      result_type operator() ( boost::logic::tribool val ) const {
        if( boost::logic::indeterminate(val) ) {
          return "X";
        } else {
          return val ? "1" : "0";
        }
      }

      result_type operator() ( std::vector< boost::logic::tribool > val ) const {
        unsigned size = val.size();
        std::string s(size,'\0');
        for (unsigned i = 0; i < size; ++i) {
          if( boost::logic::indeterminate(val[i]) ) {
            s[size-i-1] = 'X';
          } else {
            s[size-i-1] = val[i] ? '1' : '0';
          }
        }
        return s;
      }

      result_type operator() ( std::vector< bool > val ) const {
        unsigned size = val.size();
        std::string s(size,'\0');
        for (unsigned i = 0; i < size; ++i) {
          s[size-i-1] = val[i] ? '1' : '0';
        }
        return s;
      }

      result_type operator() ( boost::dynamic_bitset<> const & val ) const
      {
        std::string s(val.size(), '\0');
        boost::to_string(val, s);
        s.begin(), s.end();
        return s;
      }

    };

    template<typename Integer>
    struct as_integer {

      typedef Integer result_type;
      typedef boost::optional< boost::function0<bool> > Rng;

      as_integer ( Rng rng ) : _rng(rng) {}

      result_type operator() ( bool b ) const {
        if (boost::is_signed<Integer>::value) {
          return -(Integer)b;
        } else {
          return b;
        }
      }

      result_type operator() ( boost::logic::tribool const & b ) const {
        if(_rng && boost::logic::indeterminate(b))
          return random_bit();
        else if (boost::is_signed<Integer>::value) {
          return b ? -1 : 0;
        } else {
          return b ? 1 :0;
        }
      }

      result_type operator() ( std::vector< boost::logic::tribool > const & val ) const
      {
        Integer ret = 0;
        bool isSigned = boost::is_signed<Integer>::value && val.back();
        if( isSigned ) ret = -1 ;
        for (unsigned i = 0; i < val.size(); ++i) {
          ret ^= Integer( ((bool)(*this)(val[i]))^isSigned ? 1 : 0) << i;
        }
        return ret;
      }

      result_type operator() ( std::vector< bool > const & val ) const
      {
        Integer ret = 0;
        bool isSigned = boost::is_signed<Integer>::value && val.back();
        if( isSigned ) ret = -1 ;
        for (unsigned i = 0; i < val.size(); ++i) {
          ret ^= Integer( val[i]^isSigned ? 1 : 0) << i;
        }
        return ret;
      }

      result_type operator() ( std::string const & val ) const
      {
        Integer ret = 0;
        if( boost::is_signed<Integer>::value && val[0] == '1' ) ret = -1;
        for (std::string::const_iterator ite = val.begin();  ite != val.end(); ++ite)
        {
          ret <<=1;
          switch ( *ite ) {
            case '0':
              break;
            case '1':
              ret |= Integer(1);
              break;
            default:
              ret |= Integer( _rng && random_bit());
          }
        }
        return ret;
      }

      result_type operator() ( boost::dynamic_bitset<> const & val ) const
      {
        const bool issigned = boost::is_signed<Integer>::value;
        if( !issigned && sizeof(Integer) <= sizeof(unsigned long) ) {
          return static_cast<result_type>( val.to_ulong() );
        } else {
          Integer ret = 0;
          bool isSigned = boost::is_signed<Integer>::value && val[val.size()-1];
          if( isSigned ) ret = -1 ;
          for (unsigned i = 0; i < val.size(); ++i) {
            ret ^= Integer( val[i]^isSigned ? 1 : 0) << i;
          }
          return ret;
        }
      }

      bool random_bit() const {
        return (*_rng)();
      }
      Rng _rng;
    };

    struct check_if_X
    {
      typedef bool result_type; 

      template<typename T>
      result_type operator() ( T const & v ) const {
        return false;
      }

      result_type operator() ( boost::logic::tribool val ) const {
        return boost::logic::indeterminate(val);
      }
        
      result_type operator() ( std::vector< boost::logic::tribool > val ) const {
        unsigned size = val.size();
        for (unsigned i = 0; i < size; ++i) {
          if( boost::logic::indeterminate(val[i]) )
            return true;
        }
        return false;
      }

      result_type operator() ( std::string val ) const {
        unsigned size = val.size();
        for (unsigned i = 0; i < size; ++i) {
          if( val[i] == 'x' || val[i] == 'X' )
            return true;
        }
        return false;
      }
    };

    public:
      typedef boost::mpl::vector<
        bool
        , std::vector<boost::logic::tribool>
        , std::vector<bool>
        , std::string
        , boost::logic::tribool
        , boost::dynamic_bitset<> 
        > result_types_list;
      typedef boost::make_variant_over<result_types_list>::type result_type;

    public:
      result_wrapper() : r (std::string("X")) { }
      result_wrapper( result_type r ) : r (r) { }
      result_wrapper( boost::logic::tribool t ) : r (t) { }
      result_wrapper( bool b ) : r (boost::logic::tribool(b)) { }
      result_wrapper( std::string const & s ) : r (boost::algorithm::to_upper_copy(s)) { }
      result_wrapper( const char* s ) : r(boost::algorithm::to_upper_copy(std::string(s))) { }
      result_wrapper( const char c ) 
      : r (c=='1' ? boost::logic::tribool(true) 
        : (c=='0' ? boost::logic::tribool(false) 
        : boost::logic::tribool(boost::logic::indeterminate))
        )
      { }
      result_wrapper( unsigned long value, unsigned long width )
      : r( boost::dynamic_bitset<>(width, value) )
      { }

      operator std::vector<bool> () const {
        return boost::apply_visitor(as_vector_bool(), r);
      }

      operator std::vector<boost::logic::tribool> () const {
        return boost::apply_visitor(as_vector_tribool(), r);
      }

      operator std::string () const {
        return boost::apply_visitor(as_string(), r);
      }

      operator boost::dynamic_bitset<> () const {
        std::vector<boost::logic::tribool> val = *this;
        boost::dynamic_bitset<> ret(val.size());
        for (unsigned i = 0; i < val.size(); ++i) {
          ret[i]=val[i];
        }
        return ret;
      }

      result_wrapper & throw_if_X() {
        if ( boost::apply_visitor( check_if_X(), r) ) {
          throw std::string("contains X");
        }
        return *this;
      }

      typedef boost::optional< boost::function0<bool> > Rng;

      result_wrapper & randX( Rng rng = Rng() ) {
        _rng=rng;
        return *this;
      }

      template< typename Integer> 
      operator Integer () const {
        //BOOST_CONCEPT_ASSERT(( boost::Integer<Integer> ));
        return boost::apply_visitor(as_integer<Integer>(_rng), r);
      } 

      operator boost::logic::tribool () const {
        return boost::apply_visitor(as_tribool(), r);
      }

      friend std::ostream &
      operator<< (std::ostream & out, result_wrapper const & rw) {
        std::string o = rw;
        out << o ;
        return out;
      }


    protected:
    result_type r;
    Rng _rng;
  };
  
} // namespace metaSMT

//  vim: ft=cpp:ts=2:sw=2:expandtab
