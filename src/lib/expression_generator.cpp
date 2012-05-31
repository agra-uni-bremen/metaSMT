#define BOOST_VARIANT_VISITATION_UNROLLING_LIMIT 60
#include "../metaSMT/expression/print_expression_generic.hpp"

namespace metaSMT {
  namespace expression {
    bool print_expression_static( std::ostream_iterator<char> &out_it,
                                  logic_expression const &expr,
                                  boost::function<std::string(unsigned)> const &table ) {
      grammar< std::ostream_iterator<char> > g(table);
      return boost::spirit::karma::generate_delimited(out_it, g, boost::spirit::ascii::space, expr);
    }
  } // expression
} // metaSMT
