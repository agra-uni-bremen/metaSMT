#pragma once

#include <boost/variant/variant.hpp>
#include "Types.hpp"

namespace metaSMT {

  namespace logic {
    template < typename Context >
    struct Expr {
      typedef boost::variant<
        logic::predicate
      , logic::QF_BV::bitvector
      , typename Context::result_type
      > type;
    }; // Expr

    template < typename Context >
    class convert_to_result_type_visitor : public boost::static_visitor<typename Context::result_type> {
    public:
      convert_to_result_type_visitor(Context &ctx)
        : ctx_(ctx)
      {}
      
      typename Context::result_type operator()(logic::predicate const &expr) const {
        return evaluate(ctx_, expr);
      }
      
      typename Context::result_type operator()(logic::QF_BV::bitvector const &expr) const {
        return evaluate(ctx_, expr);
      }
      
      typename Context::result_type operator()(typename Context::result_type const &expr) const {
        return expr;
      }
      
      Context &ctx_;
    }; // convert_to_result_type_visitor
    
    template < typename Context >
    typename Context::result_type to_result_type(Context &ctx,
                                                 typename Expr<Context>::type const &expr) {
      return boost::apply_visitor( convert_to_result_type_visitor<Context>(ctx), expr );
    }

    template < typename Type >
    class is_type_visitor : public boost::static_visitor<bool> {
    public:
      is_type_visitor() {}
      
     bool operator()(Type const &) const {
        return true;
      }
      
      template < typename OtherType >
      bool operator()(OtherType const &) const {
        return false;
      }
    }; // is_value_visitor
    
    template < typename Context, typename Type >
    bool is_value(typename Expr<Context>::type const &expr) {
      return boost::apply_visitor( is_type_visitor<Type>(), expr );
    }

    template < typename Type >
    bool is_type(type::any_type const &type) {
      return boost::apply_visitor( is_type_visitor<Type>(), type );
    }

  }  // logic

  template < typename Context >
  struct TypedSymbol;

  template < typename Context >
  class convert_to_bitvector_visitor : public boost::static_visitor<typename Context::result_type> {
  public:
    convert_to_bitvector_visitor(Context &ctx,
                                 TypedSymbol<Context> &typed_symbol)
      : ctx_(ctx)
      , s_(typed_symbol)
    {}
      
    typename Context::result_type operator()(type::Boolean const &) const {
      return evaluate(ctx_, Ite(equal(s_.eval(ctx_), True), bit1, bit0));
    }
      
    typename Context::result_type operator()(type::BitVector const &) const {
      return evaluate(ctx_, s_.eval(ctx_));
    }
    
    Context &ctx_;
    TypedSymbol<Context> &s_;
  }; // convert_to_bitvector_visitor
    
  template < typename Context >
  typename Context::result_type to_bitvector(Context &ctx, TypedSymbol<Context> &sy) {
    return boost::apply_visitor( convert_to_bitvector_visitor<Context>(ctx, sy), sy.type );
  }

  template < typename Context >
  class convert_to_bool_visitor : public boost::static_visitor<typename Context::result_type> {
  public:
    convert_to_bool_visitor(Context &ctx,
                            TypedSymbol<Context> &typed_symbol)
      : ctx_(ctx)
      , s_(typed_symbol)
    {}
      
    typename Context::result_type operator()(type::Boolean const &) const {
      return evaluate(ctx_, s_.eval(ctx_));
    }
      
    typename Context::result_type operator()(type::BitVector const &bv) const {
      //return evaluate(ctx_, Ite(nequal(s_.eval(ctx_), bvuint(0, bv.width)), True, False));
      return evaluate(ctx_, nequal(s_.eval(ctx_), bvuint(0, bv.width)));
    }
      
    Context &ctx_;
    TypedSymbol<Context> &s_;
  }; // convert_to_bool_visitor
    
  template < typename Context >
  typename Context::result_type to_bool(Context &ctx, TypedSymbol<Context> &sy) {
    return boost::apply_visitor( convert_to_bool_visitor<Context>(ctx, sy), sy.type );
  }

  template < typename Context >
  struct TypedSymbol {
    typedef typename Context::result_type result_type;

    TypedSymbol(logic::predicate p)
      : value(p)
      , type(type::Boolean())
    {}

    TypedSymbol(logic::QF_BV::bitvector bv, unsigned const w)
      : value(bv)
      , type(type::BitVector(w))
    {}

    TypedSymbol(result_type s,
                type::any_type ty)
      : value(s)
      , type(ty)
    {}

    TypedSymbol(TypedSymbol<Context> const &other)
      : value(other.value)
      , type(other.type)
    {}

    bool operator==(TypedSymbol<Context> const &other) const {
      return (value == other.value &&
              type == other.type);
    }

    typename Context::result_type eval(Context &ctx) const {
      return logic::to_result_type(ctx, value);
    }
    
    // value == predicate && type == Boolean 
    inline bool isPrimitiveBool() const {
      return logic::is_value<Context, logic::predicate>( value );
    }

    // value == bitvector && type == BitVector
    inline bool isPrimitiveBitVector() const {
      return logic::is_value<Context, logic::QF_BV::bitvector>( value );
    }

    inline bool isPrimitive() const {
      return isPrimitiveBool() || isPrimitiveBitVector();
    }

    inline bool isExpression() const {
      return logic::is_value<Context, typename Context::result_type>( value );
    }

    inline bool isBool() const {
      return logic::is_type<type::Boolean>( type );
    }

    inline bool isBitVector() const {
      return logic::is_type<type::BitVector>( type );
    }

    template < typename Type >
    inline Type getType(Type const &) const {
      return boost::get<Type>(type);
    }

    inline typename Context::result_type toBV(Context &ctx,
                                              unsigned const width) {
      if (isBool()) {
        return evaluate(ctx, zero_extend(width-1, to_bitvector(ctx, *this)));
      } else {
        type::BitVector bvtype = getType(type::BitVector());
        return evaluate(ctx, zero_extend(width-bvtype.width, to_bitvector(ctx, *this)));
      }
    }

    inline typename Context::result_type toBV(Context &ctx) {
      return to_bitvector(ctx, *this);
    }

    inline typename Context::result_type toBool(Context &ctx) {
      return to_bool(ctx, *this);
    }

    typename logic::Expr<Context>::type value;
    type::any_type type;
  }; // TypedSymbol
}
