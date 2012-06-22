#pragma once

#include "SMT_Graph.hpp"
#include <boost/graph/graphviz.hpp>
#include <boost/variant.hpp>
#include <boost/tuple/tuple_io.hpp>
#include <ostream>

namespace metaSMT {

  struct VertexDecorator
  {
    typedef void result_type;
    typedef boost::graph_traits<SMT_Graph>::vertex_descriptor VertexT;

    VertexDecorator( const SMT_Graph & g, VertexT const & v , std::ostream & out)
      : _g(g), _v(v), out(out) {}

    void operator()(logic::QF_BV::tag::bvbin_tag const &) {
      using namespace boost;
      out << "[ label=\"";
      out << "bvbin(" << any_cast<std::string>(get(vertex_arg, _g, _v)) << ")";
      out << "\"]";
    }

    void operator()(logic::QF_BV::tag::bvhex_tag const &) {
      using namespace boost;
      out << "[ label=\"";
      out << "bvhex(" << any_cast<std::string>(get(vertex_arg, _g, _v)) << ")";
      out << "\"]";
    }

    void operator()(logic::QF_BV::tag::bvuint_tag const &) {
      using namespace boost;
      out << "[ label=\"";
      out << "bvuint" << any_cast<tuple< unsigned long, unsigned long> >(get(vertex_arg, _g, _v));
      out << "\"]";
    }

    void operator()(logic::QF_BV::tag::bvsint_tag const &) {
      using namespace boost;
      out << "[ label=\"";
      out << "bvsint" << any_cast<tuple< long, unsigned long> >(get(vertex_arg, _g, _v));
      out << "\"]";
    }

    template <typename Tag>
    void operator()(Tag const & t ){
      using namespace boost;
      out << "[ label=\"" << out << "\"]";
    }

    private:
      const SMT_Graph & _g;
      const VertexT & _v;
      std::ostream & out;
  };

  struct DotDecorator {
    DotDecorator(const SMT_Graph & g) 
      : _g(g) { }

    typedef boost::graph_traits<SMT_Graph>::vertex_descriptor VertexT;
    typedef boost::graph_traits<SMT_Graph>::edge_descriptor   EdgeT;

    void operator()(std::ostream & out, VertexT n ) {
      VertexDecorator vd(_g, n, out);
      boost::apply_visitor(vd, boost::get(boost::vertex_tag, _g, n) );
    }

    void operator()(std::ostream & out, EdgeT e){
      using namespace boost;
      out << "[ label=\"";
      out << "IN: " << get(edge_input, _g, e);
      out << "\"]";
    }

    template <typename T2>
    void operator()(std::ostream & out, T2) const{
    }

    private:
    SMT_Graph const & _g;
  };


  inline void write_dot(std::ostream & out, SMT_Graph & g) {
    DotDecorator dotDecorator(g);
    write_graphviz(out, g, dotDecorator, dotDecorator);
  }

} // namespace metaSMT
//  vim: ft=cpp:ts=2:sw=2:expandtab
