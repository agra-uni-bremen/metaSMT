#pragma once
#include "frontend/Logic.hpp"
#include "frontend/QF_BV.hpp"
#include "support/SMT_Graph.hpp"
#include "support/dot_SMT_Graph.hpp"
#include "support/SMT_File_Writer.hpp"

#include <boost/proto/core.hpp>
#include <boost/proto/context.hpp>
#include <boost/proto/proto.hpp>
#include <boost/proto/make_expr.hpp>
#include <boost/tr1/unordered_map.hpp>
#include <boost/tuple/tuple_comparison.hpp>

#include <iostream>
#include <fstream>
#include <sstream>
#include <map>
#include <exception>

namespace proto = boost::proto;

namespace metaSMT {
 
  /**
   * \ingroup Backend
   * \class Graph_Context Graph_Context.hpp metaSMT/Graph_Context.hpp
   * \brief A graph based representation of metaSMT expressions.
   *
   * This Backend build an expression tree for the evaluated expressions.
   * It supports no commands, only evaluates expressions and returns
   * a node in the internal graph.
   * 
   * The internal graph is an SMT_Graph and can be access with graph()
   */
  struct Graph_Context 
    : proto::callable_context< Graph_Context, proto::null_context >
  {
    Graph_Context() 
    {
    }

    ~Graph_Context() {
    }

    typedef SMT_Expression result_type;

    result_type operator() (proto::tag::terminal, result_type const & expr ) {
      return expr;
    }

    result_type operator() (proto::tag::terminal, logic::QF_BV::tag::var_tag const & tag ) {
      VariableLookupT::const_iterator ite
        = _variables.find(tag.id);
      if ( ite!= _variables.end() ) {
        return ite->second;
      } else {
        SMT_Expression ret = boost::add_vertex(_g);
        boost::put(boost::vertex_tag, _g, ret, tag);
        _variables.insert( std::make_pair(tag.id, ret) );
        return ret;
      }
    }

    result_type operator() (proto::tag::terminal, logic::Array::tag::array_var_tag const & tag ) {
      if ( tag.id == 0 ) {
        throw std::runtime_error("Uninitialized array variable");
      }

      VariableLookupT::const_iterator ite
        = _variables.find(tag.id);
      if ( ite!= _variables.end() ) {
        return ite->second;
      } else {
        SMT_Expression ret = boost::add_vertex(_g);
        boost::put(boost::vertex_tag, _g, ret, tag);
        _variables.insert( std::make_pair(tag.id, ret) );
        return ret;
      }
    }

    template<typename Upper, typename Lower, typename Expr>
    result_type operator() (logic::QF_BV::tag::extract_tag tag
        , Upper upper
        , Lower lower
        , Expr arg
    ) {
      result_type node = proto::eval(arg, *this);
      SMT_Expression ret = boost::add_vertex(_g);
      boost::put(boost::vertex_tag, _g, ret, tag);
      boost::put(boost::vertex_arg, _g, ret,
        boost::tuple<unsigned long, unsigned long>(
          proto::value(upper), proto::value(lower)) 
      );
      SMT_Edge e; bool b;
      boost::tie(e, b) = boost::add_edge(ret, node, _g);
      put(boost::edge_input, _g, e, 1);
      return ret;
    }

    template<typename Width, typename Expr >
    result_type operator() (logic::QF_BV::tag::zero_extend_tag tag
        , Width width
        , Expr arg
    ) {
      result_type node = proto::eval(arg, *this);
      SMT_Expression ret = boost::add_vertex(_g);
      boost::put(boost::vertex_tag, _g, ret, tag);
      boost::put(boost::vertex_arg, _g, ret,
          proto::value(width)
      );
      SMT_Edge e; bool b;
      boost::tie(e, b) = boost::add_edge(ret, node, _g);
      put(boost::edge_input, _g, e, 1);
      return ret;
    }

    template<typename Width, typename Expr >
    result_type operator() (logic::QF_BV::tag::sign_extend_tag tag
        , Width width
        , Expr arg
    ) {
      result_type node = proto::eval(arg, *this);
      SMT_Expression ret = boost::add_vertex(_g);
      boost::put(boost::vertex_tag, _g, ret, tag);
      boost::put(boost::vertex_arg, _g, ret,
          proto::value(width)
      );
      SMT_Edge e; bool b;
      boost::tie(e, b) = boost::add_edge(ret, node, _g);
      put(boost::edge_input, _g, e, 1);
      return ret;
    }

    template<typename TagT>
    result_type operator() (proto::tag::terminal, TagT tag ) 
    {
      Tag t1 (tag);
      Op0LookupT::const_iterator ite = _op0Lookup.find( t1 );
      if( ite != _op0Lookup.end() ) {
        return ite->second;
      }
      SMT_Expression ret = boost::add_vertex(_g);
      boost::put(boost::vertex_tag, _g, ret, tag);
      _op0Lookup.insert( std::make_pair( t1, ret) );
      return ret;
    }

    template<typename TAG, typename Expr1, typename Expr2>
    result_type operator() (TAG tag, Expr1 e1, Expr2 e2)
    {
      Tag t1 (tag);
      result_type arg1 = proto::eval(e1, *this);
      result_type arg2 = proto::eval(e2, *this);
      Op2LookupT::const_iterator ite =
        _op2Lookup.find( boost::make_tuple(t1, arg1, arg2) );
      if( ite != _op2Lookup.end() ) {
        return ite->second;
      }
      result_type ret = boost::add_vertex(_g);
      boost::put(boost::vertex_tag, _g, ret, tag);
      boost::add_edge(ret, arg1, _g);
      SMT_Edge e; bool b;
      boost::tie(e, b) = boost::add_edge(ret, arg2, _g);
      put(boost::edge_input, _g, e, 1);
      _op2Lookup.insert( std::make_pair( 
        boost::make_tuple( t1, arg1, arg2 ),
        ret
      ));
      return ret;
    }

    template<typename TAG, typename Expr1, typename Expr2, typename Expr3>
    result_type operator() (TAG tag, Expr1 e1, Expr2 e2, Expr3 e3)
    {
      Tag t1 (tag);
      result_type arg1 = proto::eval(e1, *this);
      result_type arg2 = proto::eval(e2, *this);
      result_type arg3 = proto::eval(e3, *this);
      Op3LookupT::const_iterator ite =
        _op3Lookup.find( boost::make_tuple(t1, arg1, arg2, arg3) );
      if( ite != _op3Lookup.end() ) {
        return ite->second;
      }
      result_type ret = boost::add_vertex(_g);
      boost::put(boost::vertex_tag, _g, ret, tag);
      boost::add_edge(ret, arg1, _g);
      SMT_Edge e; bool b;
      boost::tie(e, b) = boost::add_edge(ret, arg2, _g);
      put(boost::edge_input, _g, e, 1);
      boost::tie(e, b) = boost::add_edge(ret, arg3, _g);
      put(boost::edge_input, _g, e, 2);
      _op3Lookup.insert( std::make_pair( 
        boost::make_tuple( t1, arg1, arg2, arg3),
        ret
      ));
      return ret;
    }


    template< typename Expr1, typename Expr2>
    result_type operator() (logic::QF_BV::tag::bvuint_tag const & tag
        , Expr1 value
        , Expr2 bw
    ) {
      const unsigned long val   = proto::value(value);
      const unsigned long width = proto::value(bw);

      if(width==1) {
        // return bit0/1
        if (val == 1) {
          return (*this)(proto::tag::terminal(), logic::QF_BV::tag::bit1_tag());
        } else {
          return (*this)(proto::tag::terminal(), logic::QF_BV::tag::bit0_tag());
        }
      }
  
      ConstantLookupT::const_iterator ite
        = _constants.find( boost::make_tuple(tag, val, width) );
      if ( ite != _constants.end()) {
        return ite->second;
      }
      SMT_Expression ret = boost::add_vertex(_g);
      boost::put(boost::vertex_tag, _g, ret, tag);
      boost::put(boost::vertex_arg, _g, ret, boost::make_tuple( val, width) );
      _constants.insert( std::make_pair( boost::make_tuple(tag, val, width), ret) );
      return ret;
    }

    template< typename Expr1, typename Expr2>
    result_type operator() (logic::QF_BV::tag::bvsint_tag const & tag
        , Expr1 value
        , Expr2 bw
    ) {
      const long val            = proto::value(value);
      const unsigned long width = proto::value(bw);

      if(width==1) {
        // return bit0/1
        if (val == 0) {
          return (*this)(proto::tag::terminal(), logic::QF_BV::tag::bit0_tag());
        } else {
          return (*this)(proto::tag::terminal(), logic::QF_BV::tag::bit1_tag());
        }
      }
  
      ConstantLookupT::const_iterator ite
        = _constants.find( boost::make_tuple(tag, val, width) );
      if ( ite != _constants.end()) {
        return ite->second;
      }
      SMT_Expression ret = boost::add_vertex(_g);
      boost::put(boost::vertex_tag, _g, ret, tag);
      boost::put(boost::vertex_arg, _g, ret, boost::make_tuple( val, width) );
      _constants.insert( std::make_pair( boost::make_tuple(tag, val, width), ret) );
      return ret;
    }

    template< typename Expr1>
    result_type operator() (logic::QF_BV::tag::bvbin_tag tag
        , Expr1 value
    ) {
      const std::string val = proto::value(value);

      if(val.size()==1) {
        // return bit0/1
        if (val[0] == '0') {
          return (*this)(proto::tag::terminal(), logic::QF_BV::tag::bit0_tag());
        } else {
          return (*this)(proto::tag::terminal(), logic::QF_BV::tag::bit1_tag());
        }
      }
  
      ConstantLookupT::const_iterator ite
        = _constants.find( boost::make_tuple(tag, val) );
      if ( ite != _constants.end()) {
        return ite->second;
      }
      SMT_Expression ret = boost::add_vertex(_g);
      boost::put(boost::vertex_tag, _g, ret, tag);
      boost::put(boost::vertex_arg, _g, ret, proto::value(value));
      _constants.insert( std::make_pair( boost::make_tuple(tag, val), ret ) );
      return ret;
    }
    
    template< typename Expr1>
    result_type operator() (logic::QF_BV::tag::bvhex_tag tag
        , Expr1 value
    ) {
      const std::string val = proto::value(value);

      ConstantLookupT::const_iterator ite
        = _constants.find( boost::make_tuple(tag, val) );
      if ( ite != _constants.end()) {
        return ite->second;
      }
      SMT_Expression ret = boost::add_vertex(_g);
      boost::put(boost::vertex_tag, _g, ret, tag);
      boost::put(boost::vertex_arg, _g, ret, proto::value(value));
      _constants.insert( std::make_pair( boost::make_tuple(tag, val), ret ) );
      return ret;
    }
    
    template< typename TAG, typename Expr1>
    result_type operator() (TAG tag, Expr1 const & e1) 
    {
      result_type arg1 = proto::eval(e1, *this);
      Op1LookupT::const_iterator ite =
        _op1Lookup.find( boost::make_tuple(tag, arg1) );
      if( ite != _op1Lookup.end() ) {
        return ite->second;
      }
      result_type ret = boost::add_vertex(_g);
      boost::put(boost::vertex_tag, _g, ret, tag);
      boost::add_edge(ret, arg1, _g);
      _op1Lookup.insert( std::make_pair( 
        boost::make_tuple( tag, arg1 ),
        ret
      ));
      return ret;
    }

    /**
     * \return The internal Graph.
     */
    SMT_Graph const & graph() { return _g; } 

    template<typename Stream>
    void write_dot(Stream & out ){
      ::metaSMT::write_dot(out, _g );
    }

    template<typename Stream>
    void write_smt(Stream & out, std::vector<SMT_Expression> const &assertions) {
      ::metaSMT::write_smt(out, _g, assertions);
    }

    private:
      SMT_Graph _g;

    private:
      typedef boost::variant <
          nil
        , boost::tuple< logic::QF_BV::tag::bvuint_tag, unsigned long , unsigned long >
        , boost::tuple< logic::QF_BV::tag::bvsint_tag, long , unsigned long >
        , boost::tuple< logic::QF_BV::tag::bvbin_tag, std::string >
        , boost::tuple< logic::QF_BV::tag::bvhex_tag, std::string >
      > ConstantOpT;

      typedef std::tr1::unordered_map<unsigned, result_type> VariableLookupT;
      typedef std::map< ConstantOpT, result_type> ConstantLookupT;
      typedef std::map< Tag, result_type > Op0LookupT;
      typedef std::map< boost::tuple<Tag, result_type>, result_type > Op1LookupT;
      typedef std::map< boost::tuple<Tag, result_type, result_type>, result_type > Op2LookupT;
      typedef std::map< boost::tuple<Tag, result_type, result_type, result_type>, result_type > Op3LookupT;
      VariableLookupT _variables;
      ConstantLookupT _constants;
      Op0LookupT _op0Lookup;
      Op1LookupT _op1Lookup;
      Op2LookupT _op2Lookup;
      Op3LookupT _op3Lookup;
     
  }; // Graph_Context

  template <typename Expr>
  SMT_Expression evaluate( Graph_Context & ctx, Expr const & e ) {
    check(e);
    return  proto::eval(e, ctx) ;
  }
} // namespace metaSMT 
//  vim: ft=cpp:ts=2:sw=2:expandtab
