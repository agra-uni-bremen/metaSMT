#pragma once

#include "metaSMT/tags/Logics.hpp"

#define _BACKWARD_BACKWARD_WARNING_H
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/adjacency_list.hpp>
#undef _BACKWARD_BACKWARD_WARNING_H
#include <boost/function.hpp>
#include <boost/any.hpp>

namespace boost {
  enum edge_input_t { edge_input };
  BOOST_INSTALL_PROPERTY (edge, input);

  enum vertex_tag_t { vertex_tag };
  BOOST_INSTALL_PROPERTY (vertex, tag);

  enum vertex_arg_t { vertex_arg };
  BOOST_INSTALL_PROPERTY (vertex, arg);
}

namespace metaSMT {
  
  /* define properties on edges */
  typedef boost::property <boost::edge_input_t, size_t> edge_input_property;
  typedef edge_input_property SMT_Edge_t;

  /* define properties on Vertices */
  typedef boost::property <boost::vertex_arg_t, boost::any > vertex_arg_property;
  typedef boost::property <boost::vertex_tag_t, metaSMT::Tag, vertex_arg_property> vertex_tag_property;
  typedef vertex_tag_property SMT_Vertex_t;

  typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::directedS
                              , SMT_Vertex_t
                              , SMT_Edge_t
                              > SMT_Graph  ;

  typedef boost::graph_traits<SMT_Graph >::vertex_descriptor SMT_Expression;
  typedef boost::graph_traits<SMT_Graph >::edge_descriptor   SMT_Edge;

  
} /* namespace metaSMT */

//  vim: ft=cpp:ts=2:sw=2:expandtab
