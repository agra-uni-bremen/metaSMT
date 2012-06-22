#pragma once
#include "../tags/SAT.hpp"
#include <boost/mpl/int.hpp>
#include <boost/fusion/include/vector.hpp>
#include <boost/fusion/include/as_vector.hpp>
#include <boost/fusion/include/joint_view.hpp>
#include <boost/fusion/include/single_view.hpp>

#include <boost/proto/core.hpp>
  
namespace metaSMT {
  namespace transform {
    namespace proto = boost::proto;

    struct satClauseArity
      : proto::or_<
            proto::when<proto::terminal<proto::_>, boost::mpl::int_<1>()>
          , proto::otherwise<proto::fold<proto::_, boost::mpl::int_<0>(), boost::mpl::plus<proto::_state, satClauseArity>()> >
      > {};


    struct satClause 
      : proto::or_<
        proto::when<
          proto::terminal<proto::_>
          , boost::fusion::single_view<
            proto::_value
          > ( 
            proto::_value
          )
        >
        , proto::when<
            proto::plus<satClause, satClause>
          , boost::fusion::joint_view<
              boost::add_const<satClause(proto::_left) >
            , boost::add_const<satClause(proto::_right) >
          >(satClause(proto::_left), satClause(proto::_right))
        >
        , proto::when<
            proto::negate< proto::negate<proto::_> >
          , satClause(proto::_child(proto::_child))
        >
        , proto::when<
            proto::negate< proto::terminal<proto::_> >
          , boost::fusion::single_view<
              proto::call<std::negate<SAT::tag::lit_tag> >(
                proto::_value(proto::_child)
              )
            > ( 
              proto::call<std::negate<SAT::tag::lit_tag> >(
                proto::_value(proto::_child)
              )
            )
        >
     > {};


  } /* transform */
} /* metaSMT */

