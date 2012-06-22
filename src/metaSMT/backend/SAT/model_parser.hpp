#include <boost/spirit/include/qi.hpp>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_io.hpp>
#include <boost/fusion/adapted/boost_tuple.hpp>
#include <string>
#include <vector>

namespace metaSMT {
  namespace SAT {
    /**
     *  first element is the result (SATISFIABLE)
     *  second is the assignment.
     **/
    typedef boost::tuple< std::string, std::vector< int > > result_tuple;
    
    // debug code
    //template< typename O>
    //O& operator<< (O& o, std::vector< int > const & v) {
    //  BOOST_FOREACH(int i, v) {
    //    o << i << ' ';
    //  }
    //  return o;
    //}

    template< typename Iterator >
    struct model_grammar : boost::spirit::qi::grammar<Iterator, result_tuple()>
    {
      model_grammar() : model_grammar::base_type(start)
      {
        using boost::spirit::qi::lit;
        using boost::spirit::qi::char_;
        using boost::spirit::qi::int_;
        using boost::spirit::qi::eol;
        using boost::spirit::qi::attr;

        start = 
             *comment
          >> result
          >> *comment 
          >> -lit("v ") >> ( int_ % ((eol >> -lit("v ")) | lit(' ')) ) >> +eol
          >> *comment 
          ;
        result =   -lit("s ") >> *(char_ - (eol | ' ')) >> +eol;
        comment = -(lit('c') >> *(char_ - eol)) >> +eol;
  
        //start.name("start");
        //comment.name("comment");
        //result.name("result");

        //debug(start);
        //debug(comment);
        //debug(result);
      }

      boost::spirit::qi::rule<Iterator, result_tuple()> start;
      boost::spirit::qi::rule<Iterator, std::string()> result;
      boost::spirit::qi::rule<Iterator > comment;

    };
  } /* SA */
} /* metaSMT */
