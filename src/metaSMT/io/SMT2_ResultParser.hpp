#pragma once

#include <boost/spirit/include/qi.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_io.hpp>
#include <boost/fusion/adapted/boost_tuple.hpp>
#include <string>
#include <vector>

namespace metaSMT {

  namespace io {

    namespace qi = boost::spirit::qi;

    template< typename Iterator >
    struct smt2_response_grammar : qi::grammar<Iterator, std::string()> {
      smt2_response_grammar() : smt2_response_grammar::base_type(start) {
        using qi::omit;
        using qi::lit;
        using qi::char_;
        using qi::int_;
        using qi::eol;
        using qi::attr;
        using qi::space;
        using qi::alnum;

        // See: SMT-LIB 2 - Section 3.1: Symbol
        quotted_symbol =
          omit[ lit('|') >> *( char_-lit('|') ) >> lit('|') ]
          ;

        simple_symbol =
          omit[ +(alnum | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' | '+' | '=' | '<' | '>' | '.' | '?' | '/') ]
          ;

        symbol_name =
          omit[ quotted_symbol | simple_symbol ]
          ;

        select_expr =
          lit("(select") >> *( char_-lit(')') ) >> lit("))")
          ;

        start =
          lit("((") >> (symbol_name | select_expr) >> omit[ *space ] >> +( char_('#') | alnum ) >> lit("))")
          ;

        //start.name("start");
        //debug(start);
      }

      qi::rule<Iterator> quotted_symbol;
      qi::rule<Iterator> simple_symbol;
      qi::rule<Iterator> symbol_name;
      qi::rule<Iterator> select_expr;
      qi::rule<Iterator, std::string()> start;
    }; // smt2_response_grammar

  } // io

} // metaSMT
