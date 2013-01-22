#pragma once
#include <boost/spirit/include/support_utree.hpp>
#include <boost/spirit/include/qi.hpp>
#include <istream>

namespace metaSMT {
  namespace smt2 {
    namespace spirit   = boost::spirit;
    namespace qi       = boost::spirit::qi;
    namespace phoenix  = boost::phoenix;
    namespace standard = boost::spirit::standard;
    namespace ascii    = boost::spirit::ascii;

    namespace detail {
      template<typename Iterator>
      struct whitespace : qi::grammar< Iterator >  {
        whitespace()
          : whitespace::base_type(start) {
          using standard::space;
          using standard::char_;
          using qi::eol;

          start = space | ( ';' >> *(char_ - eol) >> eol );
        }

        qi::rule<Iterator> start;
      }; // whitespace

      template < typename Iterator, typename Evaluator >
      struct parser : qi::grammar< Iterator, spirit::utree::list_type(), whitespace<Iterator> > {
        parser( Evaluator &eval )
          : parser::base_type(start)
          , evaluate(eval)
          , evaluator(eval) {

          start %= *( command );

          command %= '(' >> command_name >> *sexpr >> ')';

          sexpr %= '(' >> *sexpr >> ')' | symbol | numeral;

          symbol %= qi::lexeme [ +(qi::char_ -end_of_word ) ];

          numeral %= qi::uint_;

          command_name %= qi::lexeme [ +(qi::char_ - end_of_word ) ];

          end_of_word %= qi::space | qi::char_(")");

          start.name( "start" );
          command.name( "command" ) ;
          sexpr.name( "s-expr" );
          symbol.name( "symbol" );
          numeral.name( "numeral" );
          command_name.name( "command_name" );

#if 0
          qi::debug ( start);
          qi::debug ( command );
          qi::debug ( sexpr );
          qi::debug ( symbol );
          qi::debug ( numeral );
          qi::debug ( command_name );
#endif
        }

        qi::rule<Iterator, spirit::utree::list_type(), whitespace< Iterator > > start;
        qi::rule<Iterator, spirit::utree(), whitespace< Iterator > > numeral, sexpr;
        qi::rule<Iterator, spirit::utf8_symbol_type(), whitespace< Iterator > > command_name;
        qi::rule<Iterator, spirit::utf8_string_type(), whitespace< Iterator > > symbol;
        qi::rule<Iterator, spirit::utree::list_type(), whitespace< Iterator> > command;
        qi::rule<Iterator > end_of_word;

        phoenix::function<Evaluator> const evaluate;
        Evaluator& evaluator;
      }; // parser
    } // detail

    template < typename Evaluator >
    class SMT2Parser {
    public:
      SMT2Parser( Evaluator &evaluator )
        : evaluator(evaluator)
      {}

      bool parse( std::istream &instream, spirit::utree::list_type &ast ) {
        if ( !instream.good() ) {
          return false;
        }

        instream.unsetf ( std::ios::skipws );

        spirit::istream_iterator begin(instream);
        spirit::istream_iterator end;

        detail::parser<spirit::istream_iterator, Evaluator> p( evaluator );
        detail::whitespace<spirit::istream_iterator> ws;
        bool r = phrase_parse( begin, end, p, ws, ast );
        if ( r && begin == end ) {
          return true;
        }
        else {
          std::cerr << "ERROR: Parsing failed!" << std::endl;
          std::cerr << "Stop at:" << std::string(begin, end) << std::endl;
          return false;
        }
      }

    private:
      Evaluator &evaluator;
    }; // SMT2Parser

  } // smt2
} // metaSMT
