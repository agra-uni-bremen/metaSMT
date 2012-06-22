#pragma once

#include "../result_wrapper.hpp"

#include <boost/spirit/include/qi.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_io.hpp>
#include <boost/fusion/adapted/boost_tuple.hpp>
#include <string>

namespace metaSMT {
  namespace smt2 {
    
    template< typename Iterator >
    struct smt2_result_grammar : boost::spirit::qi::grammar<Iterator, result_wrapper()>
    {
      smt2_result_grammar() : smt2_result_grammar::base_type(start)
      {
        using boost::spirit::qi::lit;
        using boost::spirit::qi::uint_;
        using boost::spirit::qi::eol;
        using boost::spirit::qi::attr;
        using boost::spirit::qi::labels::_1;
        using boost::spirit::qi::labels::_2;
        using boost::spirit::qi::labels::_val;

        start = boolean ;// | bitvector;
          ;
        
        boolean = 
            lit("(true)") >> attr(result_wrapper(true))
          | lit("(false)") >> attr(result_wrapper(false))
          ;
        //bitvector =
          //(lit("((_ bv") << uint_ << " " << uint_ << "))")//[_val = construct<result_wrapper>(_1, _2)]
          ;
          
          
  
        //start.name("start");
        //boolean.name("boolean");
        //bitvector.name("bitvector");

        //debug(start);
        //debug(boolean);
        //debug(bitvector);
      }

      boost::spirit::qi::rule<Iterator, result_wrapper()> start
        , boolean
        , bitvector
        ;
      boost::spirit::qi::rule<Iterator, boost::tuple<unsigned, unsigned>()> bvint;

    };
  } /* SMT2 */
} /* metaSMT */

