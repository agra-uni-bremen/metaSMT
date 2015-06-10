#pragma once
#include "../API/Evaluator.hpp"
#include "../frontend/QF_BV.hpp"
#include "../frontend/Array.hpp"

namespace metaSMT {
  namespace support {

    template < typename Lhs, typename Rhs >
    struct ArrayEqualBase
    {
      ArrayEqualBase( Lhs lhs, Rhs rhs, unsigned index_width )
        : lhs_(lhs)
        , rhs_(rhs)
        , index_width_(index_width)
      {

      }

      Lhs lhs_;
      Rhs rhs_;
      unsigned index_width_;
    };

    template < typename Lhs, typename Rhs >
    struct ArrayEqual : ArrayEqualBase<Lhs, Rhs>
    {
      ArrayEqual( Lhs lhs, Rhs rhs, unsigned index_width )
        : ArrayEqualBase<Lhs, Rhs>(lhs, rhs, index_width)
      {
      }
    };

    template < typename Lhs, typename Rhs >
    struct ArrayNequal : ArrayEqualBase<Lhs, Rhs>
    {
      ArrayNequal( Lhs lhs, Rhs rhs, unsigned index_width )
        : ArrayEqualBase<Lhs, Rhs>(lhs, rhs, index_width)
      {
      }
    };

    template < typename Lhs, typename Rhs >
    ArrayEqual<Lhs, Rhs> array_equal( Lhs lhs, Rhs rhs, unsigned index_width )
    {
      return ArrayEqual<Lhs, Rhs>( lhs, rhs, index_width);
    }

    template < typename Lhs, typename Rhs >
    ArrayNequal<Lhs, Rhs> array_nequal( Lhs lhs, Rhs rhs, unsigned index_width )
    {
      return ArrayNequal<Lhs, Rhs>( lhs, rhs, index_width );
    }

  } // support

  template < typename Lhs, typename Rhs >
  struct Evaluator< support::ArrayEqual<Lhs, Rhs> > : public boost::mpl::true_ {

    template < typename Context >
    static typename Context::result_type
    eval(Context &ctx, support::ArrayEqual<Lhs, Rhs> const &c)
    {
      using namespace logic;
      using namespace logic::QF_BV;
      using namespace logic::Array;

      const unsigned width = c.index_width_;
      unsigned long index_limit = 1ul << width;

      typename Context::result_type result = evaluate( ctx, True );

      for ( unsigned long index = 0; index < index_limit; ++index ) {
        result = evaluate( ctx, And( result,
	  equal(
	    select( c.lhs_, bvuint(index, width) ),
	    select( c.rhs_, bvuint(index, width) )
	  ))
        );
      }

      return result;
    }
  };

  template < typename Lhs, typename Rhs >
  struct Evaluator< support::ArrayNequal<Lhs, Rhs> > : public boost::mpl::true_ {

    template < typename Context >
    static typename Context::result_type
    eval(Context &ctx, support::ArrayNequal<Lhs, Rhs> const &c)
    {
      using namespace logic;
      using namespace logic::QF_BV;
      using namespace logic::Array;

      const unsigned width = c.index_width_;
      unsigned long index_limit = 1ul << width;

      typename Context::result_type result = evaluate( ctx, False );

      for ( unsigned long index = 0; index < index_limit; ++index ) {
        result = evaluate( ctx, Or( result,
	  nequal(
	    select( c.lhs_, bvuint(index, width) ),
	    select( c.rhs_, bvuint(index, width) )
	  ))
        );
      }

      return result;
    }
  };
} // metaSMT
