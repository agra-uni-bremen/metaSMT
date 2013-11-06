#pragma once
#include "../../support/index/Logics.hpp"
#include "../../frontend/Logic.hpp"
#include "../../tags/Cardinality.hpp"
#include "../../support/cardinality.hpp"
#include <boost/tuple/tuple.hpp>

namespace metaSMT {
  namespace support {
    namespace idx {
      namespace cardtags = metaSMT::logic::cardinality::tag;

      // attribute ignore
      template < typename Context, typename Tag, typename T, typename Arg >
      typename boost::disable_if<
        typename boost::mpl::not_<
          typename boost::is_same<typename Tag::attribute, attr::ignore>::type
        >::type
      , typename Context::result_type
      >::type
      callCtx( Context *ctx, Tag const &, Arg arg, std::vector<T> const &args ) {
        assert( false && "Unsupported attribute" );
        return evaluate(*ctx, logic::False);
      }

      // attribute constant
      template < typename Context, typename Tag, typename T, typename Arg >
      typename boost::disable_if<
        typename boost::mpl::not_<
          typename boost::is_same<typename Tag::attribute, attr::constant>::type
        >::type
      , typename Context::result_type
      >::type
      callCtx( Context *ctx, Tag const &, Arg arg, std::vector<T> const &args ) {
        return (*ctx)(Tag());
      }

      // attribute unary
      template < typename Context, typename Tag, typename T, typename Arg >
      typename boost::disable_if<
        typename boost::mpl::not_<
          typename boost::is_same<typename Tag::attribute, attr::unary>::type
        >::type
      , typename Context::result_type
      >::type
      callCtx( Context *ctx, Tag const &, Arg arg, std::vector<T> const &args ) {
        return (*ctx)(Tag(), boost::proto::lit(args[0]));
      }

      // attribute binary
      template < typename Context, typename Tag, typename T, typename Arg >
      typename boost::disable_if<
        typename boost::mpl::not_<
          typename boost::is_same<typename Tag::attribute, attr::binary>::type
        >::type
      , typename Context::result_type
      >::type
      callCtx( Context *ctx, Tag const &, Arg tuple, std::vector<T> const &args ) {
        assert( args.size() == 2 );
        return (*ctx)(Tag(), boost::proto::lit(args[0]), boost::proto::lit(args[1]));
      }

      // attribute ternary
      template < typename Context, typename Tag, typename T, typename Arg >
      typename boost::disable_if<
        typename boost::mpl::not_<
          typename boost::is_same<typename Tag::attribute, attr::ternary>::type
        >::type
      , typename Context::result_type
      >::type
      callCtx( Context *ctx, Tag const &, Arg tuple, std::vector<T> const &args ) {
        return (*ctx)(Tag(), boost::proto::lit(args[0]), boost::proto::lit(args[1]), boost::proto::lit(args[2]));
      }

      // attribute left_assoc
      template < typename Context, typename Tag, typename T, typename Arg >
      typename boost::disable_if<
        typename boost::mpl::not_<
          typename boost::is_same<typename Tag::attribute, attr::left_assoc>::type
        >::type
        , typename Context::result_type
      >::type
      callCtx( Context *ctx, Tag const &, Arg tuple, std::vector<T> const &args ) {
        if ( args.size() == 2 ) {
          return (*ctx)(Tag(), boost::proto::lit(args[0]), boost::proto::lit(args[1]));
        }

        assert( args.size() >= 2 );
        return (*ctx)(Tag(), args);
      }

      // attribute right_assoc
      template < typename Context, typename Tag, typename T, typename Arg >
      typename boost::disable_if<
        typename boost::mpl::not_<
          typename boost::is_same<typename Tag::attribute, attr::right_assoc>::type
        >::type
      , typename Context::result_type
      >::type
      callCtx( Context *ctx, Tag const &, Arg tuple, std::vector<T> const &args ) {
        // std::cerr << "right_assoc" << '\n';
        if ( args.size() == 2 ) {
          return (*ctx)(Tag(), boost::proto::lit(args[0]), boost::proto::lit(args[1]));
        }
        else {
          // resolve right associativity
          assert( args.size() >= 2 );
          typename Context::result_type r = (*ctx)(Tag(),  boost::proto::lit(args[args.size()-2]), boost::proto::lit(args[args.size()-1]));
          for ( unsigned u = 0; u < args.size()-2; ++u ) {
            r = (*ctx)(Tag(), boost::proto::lit(args[args.size()-3-u]), boost::proto::lit(r));
          }
          return r;
        }
      }

      // attibrute chainable
      template < typename Context, typename Tag, typename T, typename Arg >
      typename boost::disable_if<
        typename boost::mpl::not_<
          typename boost::is_same<typename Tag::attribute, attr::chainable>::type
        >::type
      , typename Context::result_type
      >::type
      callCtx( Context *ctx, Tag const &, Arg tuple, std::vector<T> const &args ) {
        // std::cerr << "chainable" << '\n';
        std::cerr << args.size() << '\n';
        assert( args.size() == 2 );
        return (*ctx)(Tag(), boost::proto::lit(args[0]), boost::proto::lit(args[1]));
      }

      // attibrute pairwise
      template < typename Context, typename Tag, typename T, typename Arg >
      typename boost::disable_if<
        typename boost::mpl::not_<
          typename boost::is_same<typename Tag::attribute, attr::pairwise>::type
          >::type
        , typename Context::result_type
        >::type
      callCtx( Context *ctx, Tag const &, Arg tuple, std::vector<T> const &args ) {
        // std::cerr << "pairwise" << '\n';
        assert( args.size() == 2 );
        return (*ctx)(Tag(), boost::proto::lit(args[0]), boost::proto::lit(args[1]));
      }

      // zero_extend
      template < typename Context, typename T >
      typename Context::result_type
      callCtx( Context *ctx,
               bvtags::zero_extend_tag const &,
               boost::tuple<unsigned long> const &tuple,
               std::vector<T> const &args ) {
        unsigned long const w = tuple.get<0>();
        return (*ctx)(bvtags::zero_extend_tag(), boost::proto::lit(w), boost::proto::lit(args[0]));
      }

      // sign_extend
      template < typename Context, typename T >
      typename Context::result_type
      callCtx( Context *ctx,
               bvtags::sign_extend_tag const &,
               boost::tuple<unsigned long> const &tuple,
               std::vector<T> const &args ) {
        unsigned long const w = tuple.get<0>();
        return (*ctx)(bvtags::sign_extend_tag(), boost::proto::lit(w), boost::proto::lit(args[0]));
      }

      // extract
      template < typename Context, typename T >
      typename Context::result_type
      callCtx( Context *ctx,
               bvtags::extract_tag const &,
               boost::tuple<unsigned long, unsigned long> const &tuple,
               std::vector<T> const &args ) {
        unsigned long const op0 = tuple.get<0>();
        unsigned long const op1 = tuple.get<1>();
        return (*ctx)(bvtags::extract_tag(), boost::proto::lit(op0), boost::proto::lit(op1), boost::proto::lit(args[0]));
      }

      // cardinality
      template < typename Context, typename T >
      typename Context::result_type
      callCtx( Context *ctx,
               cardtags::lt_tag const &,
               boost::tuple<unsigned long> const &tuple,
               std::vector<T> const &args ) {
        unsigned long const op0 = tuple.get<0>();
        std::string const impl = get_option(*ctx, "cardinality-implementation", "bdd");
        
        std::vector< typename Context::result_type > a;
        for ( unsigned u = 0; u < args.size(); ++u ) {
          a.push_back( evaluate(*ctx, args[u]) );
        }
        
        return evaluate(*ctx,
          metaSMT::cardinality::cardinality(metaSMT::logic::cardinality::tag::lt_tag(), a, op0, impl)
        );
      }

      template < typename Context, typename T >
      typename Context::result_type
      callCtx( Context *ctx,
               cardtags::le_tag const &,
               boost::tuple<unsigned long> const &tuple,
               std::vector<T> const &args ) {
        unsigned long const op0 = tuple.get<0>();
        std::string const impl = get_option(*ctx, "cardinality-implementation", "bdd");

        std::vector< typename Context::result_type > a;
        for ( unsigned u = 0; u < args.size(); ++u ) {
          a.push_back( evaluate(*ctx, args[u]) );
        }

        return evaluate(*ctx,
          metaSMT::cardinality::cardinality(metaSMT::logic::cardinality::tag::le_tag(), a, op0, impl)
        );
      }

      template < typename Context, typename T >
      typename Context::result_type
      callCtx( Context *ctx,
               cardtags::eq_tag const &,
               boost::tuple<unsigned long> const &tuple,
               std::vector<T> const &args ) {
        unsigned long const op0 = tuple.get<0>();
        std::string const impl = get_option(*ctx, "cardinality-implementation", "bdd");

        std::vector< typename Context::result_type > a;
        for ( unsigned u = 0; u < args.size(); ++u ) {
          a.push_back( evaluate(*ctx, args[u]) );
        }

        return evaluate(*ctx,
          metaSMT::cardinality::cardinality(metaSMT::logic::cardinality::tag::eq_tag(), a, op0, impl)
        );
      }

      template < typename Context, typename T >
      typename Context::result_type
      callCtx( Context *ctx,
               cardtags::ge_tag const &,
               boost::tuple<unsigned long> const &tuple,
               std::vector<T> const &args ) {
        unsigned long const op0 = tuple.get<0>();
        std::string const impl = get_option(*ctx, "cardinality-implementation", "bdd");

        std::vector< typename Context::result_type > a;
        for ( unsigned u = 0; u < args.size(); ++u ) {
          a.push_back( evaluate(*ctx, args[u]) );
        }

        return evaluate(*ctx,
          metaSMT::cardinality::cardinality(metaSMT::logic::cardinality::tag::ge_tag(), a, op0, impl)
        );
      }

      template < typename Context, typename T >
      typename Context::result_type
      callCtx( Context *ctx,
               cardtags::gt_tag const &,
               boost::tuple<unsigned long> const &tuple,
               std::vector<T> const &args ) {
        unsigned long const op0 = tuple.get<0>();
        std::string const impl = get_option(*ctx, "cardinality-implementation", "bdd");

        std::vector< typename Context::result_type > a;
        for ( unsigned u = 0; u < args.size(); ++u ) {
          a.push_back( evaluate(*ctx, args[u]) );
        }

        return evaluate(*ctx,
          metaSMT::cardinality::cardinality(metaSMT::logic::cardinality::tag::gt_tag(), a, op0, impl)
        );
      }

      // fallback
      template < typename Context, typename Tag, typename Arg, typename T >
      typename Context::result_type
      callCtx( Context *ctx,
               Tag const &,
               Arg const &,
               T const & ) {
        assert( false && "Unsupported" );
        return typename Context::result_type();
      }

    template < typename Context, typename T, typename Arg >
    struct CallByIndexVisitor {
      CallByIndexVisitor(Context *ctx,
                         bool &found,
                         typename Context::result_type &r,
                         logic::index idx,
                         std::vector<T> const &args,
                         Arg arg)
        : ctx(ctx)
        , found(found)
        , r(r)
        , idx(idx)
        , args(args)
        , arg(arg)
      {}

      template < typename Tag >
      void operator()( Tag const & ) {
        if ( !found &&
             logic::Index<Tag>::value == idx ) {
          found = true;
          r = callCtx(ctx, Tag(), arg, args);
        }
      }

      Context *ctx;
      bool &found;
      typename Context::result_type &r;
      logic::index idx;
      std::vector<T> const &args;
      Arg arg;
    }; // CallByIndexVisitor

      template < typename Context >
      struct CallByIndex {
        CallByIndex(Context &ctx)
          : ctx(ctx)
        {}

        template < typename T, typename Arg >
        typename Context::result_type
        callByIndex( logic::index idx,
                     std::vector<T> const &args,
                     Arg p) {
          bool found = false;
          typename Context::result_type r;
          CallByIndexVisitor<Context, T, Arg> visitor(&ctx, found, r, idx, args, p);
          boost::mpl::for_each< _all_logic_tags::all_Tags >(visitor);
          assert( found );
          return r;
        }

        template < typename Arg >
        typename Context::result_type operator()( logic::index idx,
                                                  Arg arg,
                                                  std::vector< typename Context::result_type > const &args) {
          return callByIndex(idx, args, arg);
        }
      
        template < typename Arg >
        typename Context::result_type operator()( logic::index idx,
                                                  Arg arg) {
          std::vector< typename Context::result_type > args;
          return callByIndex(idx, args, arg);
        }

        template < typename T, typename Arg >
        typename Context::result_type operator()( logic::index idx,
                                                  Arg arg,
                                                  T const &op0 ) {
          std::vector< typename Context::result_type > args;
          args.push_back( op0 );
          return callByIndex(idx, args, arg);
        }

        template < typename T, typename Arg >
        typename Context::result_type operator()( logic::index idx,
                                                  Arg arg,
                                                  T const &op0,
                                                  T const &op1 ) {
          std::vector< typename Context::result_type > args;
          args.push_back( op0 );
          args.push_back( op1 );
          return callByIndex(idx, args, arg);
        }

        template < typename T, typename Arg >
        typename Context::result_type operator()( logic::index idx,
                                                  Arg arg,
                                                  T const &op0,
                                                  T const &op1,
                                                  T const &op2 ) {
          std::vector< typename Context::result_type > args;
          args.push_back( op0 );
          args.push_back( op1 );
          args.push_back( op2 );
          return callByIndex(idx, args, arg);
        }

        Context &ctx;
      }; // CallByIndex
    } // idx
  } // support
} // metaSMT
