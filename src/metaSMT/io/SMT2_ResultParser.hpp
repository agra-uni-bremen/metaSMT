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
    struct smt2_response_grammar : boost::spirit::qi::grammar<Iterator, std::string()> {
      smt2_response_grammar() : smt2_response_grammar::base_type(start) {
        using qi::omit;
        using qi::lit;
        using qi::char_;
        using qi::int_;
        using qi::eol;
        using qi::attr;
        using qi::space;
        using qi::alnum;

        start =
          lit("((") >> omit[ +( alnum | '_' ) ] >> omit[ *space ] >> +( char_('#') | alnum ) >> lit("))")
          ;
  
        //start.name("start");

        //debug(start);
      }

      boost::spirit::qi::rule<Iterator, std::string()> start;
    }; // smt2_response_grammar

  } // io

} // metaSMT
