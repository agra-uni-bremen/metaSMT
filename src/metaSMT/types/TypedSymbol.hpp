#pragma once

#include <boost/variant/variant.hpp>
#include "../frontend/Logic.hpp"
#include "../frontend/QF_BV.hpp"
#include "../frontend/Array.hpp"
#include "../tags/QF_BV.hpp"
#include "Types.hpp"

namespace metaSMT {
  namespace type {
    /* Forward TypedSymbol */
    template < typename Context >
    struct TypedSymbol;
  } // type
} // metaSMT

#include "Evaluator.hpp"

namespace metaSMT {

  namespace type {

    /**
     * \brief symbols with type information
     *
     * TypedSymbols annotate metaSMT's primitive symbols (predicate,
     * bitvector, array, and Context::result_type) with additional
     * type information (Boolean, BitVector, or Array).
     *
     * The type information is especially useful when expressions
     * become evaluated and stored as Context::result_types.
     * Additionally, TypedSymbols allow for easy conversion from one
     * type to another, e.g., predicate to bitvector.
     *
     * *Warning*: The Context in TypedSymbol<Context> and
     * Context::result_type must never change!
     *
     * \code
     *  // create typed symbol from predicate
     *  TypedSymbol<ContextType> p(new_variable());
     *
     *  // create typed symbol from bitvector primitive
     *  unsigned char const w = 32;
     *  TypedSymbol<ContextType> bv(new_bitvector(w), w);
     *
     *  // create typed symbol from Context::result_type
     *  typename Context::result_type r = bv.eval(ctx);
     *  TypedSymbol<Context> expr(r, type::BitVector(w));
     *
     * \endcode
     * \ingroup type
     * \defgroup TypedSymbol TypedSymbol
     * @{
     */

    namespace bv = ::metaSMT::logic::QF_BV;
    namespace ary = ::metaSMT::logic::Array;

    /** \cond **/
    namespace detail {
      template < typename Context >
      struct Expr {
        typedef boost::variant<
          logic::predicate
        , bv::bitvector
        , ary::array
        , typename Context::result_type
        > type;
      }; /* Expr */

      template < typename Context >
      class convert_to_result_type_visitor
        : public boost::static_visitor<typename Context::result_type> {
      public:
        convert_to_result_type_visitor(Context &ctx)
          : ctx_(ctx)
        {}

        typename Context::result_type
        operator()(logic::predicate const &expr) const {
          return evaluate(ctx_, expr);
        }

        typename Context::result_type
        operator()(bv::bitvector const &expr) const {
          return evaluate(ctx_, expr);
        }

        typename Context::result_type
        operator()(ary::array const &expr) const {
          return evaluate(ctx_, expr);
        }

        typename Context::result_type
        operator()(typename Context::result_type const &expr) const {
          return expr;
        }

        Context &ctx_;
      }; /* convert_to_result_type_visitor */

      /**
       * \brief Evaluates an Expr and returns Context::result_type
       * \param expr The expression
       * \param ctx The metaSMT Context
       * \return the evaluated expression
       *
       */
      template < typename Context >
      typename Context::result_type to_result_type(Context &ctx,
                                                   typename Expr<Context>::type const &expr) {
        return boost::apply_visitor( convert_to_result_type_visitor<Context>(ctx),
                                     expr );
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
      }; /* is_value_visitor */

      /**
       * \brief Compare value
       * \param expr The expression
       * \return true iff expr corresponds to Type
       *
       */
      template < typename Context, typename Type >
      bool is_value(typename Expr<Context>::type const &expr) {
        return boost::apply_visitor( is_type_visitor<Type>(), expr );
      }

      /**
       * \brief Compare type
       * \param type The type
       * \return true iff type corresponds to Type
       *
       */
      template < typename Type >
      bool is_type(any_type const &type) {
        return boost::apply_visitor( is_type_visitor<Type>(), type );
      }

      template < typename Context >
      class convert_to_bitvector_visitor
        : public boost::static_visitor<typename Context::result_type> {
      public:
        convert_to_bitvector_visitor(Context &ctx,
                                     TypedSymbol<Context> const &typed_symbol)
          : ctx_(ctx)
          , s_(typed_symbol)
        {}

        typename Context::result_type operator()(Boolean const &) const {
          return evaluate(ctx_, logic::Ite(s_.eval(ctx_),
                                    bv::bit1, bv::bit0));
        }

        typename Context::result_type operator()(BitVector const &) const {
          return evaluate(ctx_, s_.eval(ctx_));
        }

        typename Context::result_type operator()(type::Array const &a) const {
          unsigned const index_width = a.index_width;
          unsigned const max_index = 1 << index_width;
          typename Context::result_type r =
            evaluate(ctx_, ary::select(s_.eval(ctx_), bv::bvuint(0, index_width)));
          for ( unsigned long ul = 1; ul < max_index; ++ul ) {
            r = evaluate(ctx_, bv::concat(r, ary::select(s_.eval(ctx_), bv::bvuint(ul, index_width))));
          }
          return r;
        }

        // Fallback
        template < typename T >
        typename Context::result_type operator()(T const &t) const {
          assert( false );
          return evaluate(ctx_, metaSMT::logic::False);
        }

        Context &ctx_;
        TypedSymbol<Context> const &s_;
      }; // convert_to_bitvector_visitor

      /**
       * \brief Converts a TypedSymbol of Boolean type to BitVector
       * \param ctx The context to work on
       * \param sy The symbol to be converted
       * \return an expression corresponding to the converted bitvector
       *
       */
      template < typename Context >
      typename Context::result_type to_bitvector(Context &ctx,
                                                 TypedSymbol<Context> const &sy) {
        return boost::apply_visitor( convert_to_bitvector_visitor<Context>(ctx, sy),
                                     sy.type );
      }

      template < typename Context >
      class convert_to_bool_visitor
        : public boost::static_visitor<typename Context::result_type> {
      public:
        convert_to_bool_visitor(Context &ctx,
                                TypedSymbol<Context> const &typed_symbol)
          : ctx_(ctx)
          , s_(typed_symbol)
        {}

        typename Context::result_type operator()(Boolean const &) const {
          return evaluate(ctx_, s_.eval(ctx_));
        }

        typename Context::result_type operator()(BitVector const &bv) const {
          return evaluate(ctx_,
            logic::nequal(s_.eval(ctx_), bv::bvuint(0, bv.width)));
        }

        typename Context::result_type operator()(type::Array const &a) const {
          unsigned const w = a.elem_width*(1 << a.index_width);
          return evaluate(ctx_,
            logic::nequal(to_bitvector(ctx_, s_), bv::bvuint(0, w)));
        }

        // Fallback
        template < typename T >
        typename Context::result_type operator()(T const &t) const {
          assert( false );
          return evaluate(ctx_, logic::False);
        }

        Context &ctx_;
        TypedSymbol<Context> const &s_;
      }; // convert_to_bool_visitor

      /**
       * \brief Converts a TypedSymbol of BitVector type to Boolean
       * \param ctx The context to work on
       * \param sy The symbol to be converted
       * \return an expression corresponding to the converted boolean
       *
       */
      template < typename Context >
      typename Context::result_type to_bool(Context &ctx,
                                            TypedSymbol<Context> const &sy) {
        return boost::apply_visitor( convert_to_bool_visitor<Context>(ctx, sy),
                                     sy.type );
      }

    } /* detail */
    /** \endcond **/

    template < typename Context >
    struct TypedSymbol {
      typedef typename Context::result_type result_type;

      TypedSymbol(logic::predicate p)
        : value(p)
        , type(Boolean())
      {}

      TypedSymbol(bv::bitvector bv, unsigned const w)
        : value(bv)
        , type(BitVector(w))
      {}

      TypedSymbol(ary::array arr,
                  unsigned const elem_width,
                  unsigned const index_width)
        : value(arr)
        , type(type::Array(elem_width, index_width))
      {}

      template < typename Primitive >
      TypedSymbol(Primitive p,
                  any_type ty)
        : value(p)
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

      result_type eval(Context &ctx) const {
        return detail::to_result_type(ctx, value);
      }

      // value == predicate && type == Boolean
      inline bool isPrimitiveBool() const {
        return detail::is_value<Context, logic::predicate>( value );
      }

      // value == bitvector && type == BitVector
      inline bool isPrimitiveBitVector() const {
        return detail::is_value<Context, bv::bitvector>( value );
      }

      // value == array && type == Array
      inline bool isPrimitiveArray() const {
        return detail::is_value<Context, ary::array>( value );
      }

      inline bool isPrimitive() const {
        return isPrimitiveBool() || isPrimitiveBitVector() || isPrimitiveArray();
      }

      inline bool isExpression() const {
        return detail::is_value<Context,result_type>( value );
      }

      inline bool isBool() const {
        return detail::is_type<Boolean>( type );
      }

      inline bool isBitVector() const {
        return detail::is_type<BitVector>( type );
      }

      inline bool isArray() const {
        return detail::is_type<type::Array>( type );
      }

      template < typename Type >
      inline Type getType(Type const &) const {
        return boost::get<Type>(type);
      }

      template < typename Type >
      inline Type getType() const {
        return boost::get<Type>(type);
      }

      inline result_type toBV(Context &ctx) const {
        return detail::to_bitvector(ctx, *this);
      }

      inline result_type toBV(bv::tag::zero_extend_tag const &,
                              Context &ctx,
                              unsigned const width) const {
        if (isBool()) {
          return evaluate(ctx, bv::zero_extend(width-1,
                                 detail::to_bitvector(ctx, *this)));
        }
        else if (isBitVector()) {
          BitVector bvtype = getType(BitVector());
          assert(width > bvtype.width);
          return evaluate(ctx, bv::zero_extend(width-bvtype.width,
                                 detail::to_bitvector(ctx, *this)));
        }
        else {
          type::Array arraytype = getType(type::Array());
          unsigned const w = arraytype.elem_width*(1 << arraytype.index_width);
          assert(width > w);
          return evaluate(ctx, bv::zero_extend(width-w,
                                 detail::to_bitvector(ctx, *this)));
        }
      }

      inline result_type toBV(bv::tag::sign_extend_tag const &,
                              Context &ctx,
                              unsigned const width) const {
        if (isBool()) {
          return evaluate(ctx, bv::sign_extend(width-1,
                                 detail::to_bitvector(ctx, *this)));
        }
        else if (isBitVector()) {
          BitVector bvtype = getType(BitVector());
          assert(width > bvtype.width);
          return evaluate(ctx, bv::sign_extend(width-bvtype.width,
                                 detail::to_bitvector(ctx, *this)));
        }
        else {
          type::Array arraytype = getType(type::Array());
          unsigned const w = arraytype.elem_width*(1 << arraytype.index_width);
          assert(width > w);
          return evaluate(ctx, bv::sign_extend(width-w,
                                 detail::to_bitvector(ctx, *this)));
        }
      }

      inline result_type toBool(Context &ctx) const {
        return detail::to_bool(ctx, *this);
      }

      typename detail::Expr<Context>::type value;
      any_type type;

    }; /* TypedSymbol */

  } /* type */

  /**@}*/

} /* metaSMT */
