#pragma once
#include "expression.hpp"

namespace metaSMT {
  namespace expression {
    bool print_expression_static( std::ostream_iterator<char> &out_it,
                                  logic_expression const &expr,
                                  boost::function<std::string(unsigned)> const &table );
  } // expression
} // metaSMT
