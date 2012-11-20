
#pragma once

#include <istream>
#include <boost/spirit/include/support_utree.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/support_istream_iterator.hpp>
#include <boost/spirit/home/support/info.hpp>
#include <boost/spirit/include/support_line_pos_iterator.hpp>

#include <boost/foreach.hpp>

namespace metaSMT
{
  namespace smt2
  {
    namespace spirit   = boost::spirit;
    namespace qi       = boost::spirit::qi;
    namespace phoenix  = boost::phoenix;
    namespace standard = boost::spirit::standard;
    namespace ascii    = boost::spirit::ascii;

    using boost::spirit::utree;
    using boost::spirit::utree_type;
    using boost::spirit::info; 

    namespace detail
    {
      bool is_list_node ( utree const& u )
      {
        return u.which() == utree_type::list_type; 
      }

    }

    template<typename Out>
      struct print_info
      {
        typedef boost::spirit::utf8_string string;

        print_info ( Out& out ) : out ( out ), first( true ) {}

        void element ( string const& tag, string const& value, int ) const
        {
          if (!first) 
          {
            out << ' ';
            first = false;
          }

          if ( value == "" )
            out << tag;
          else
            out << "\"" << value << '"';
        }

        Out& out;
        mutable bool first; 

      }; 

    struct expected_component : std::exception
    {
      std::string msg;

      expected_component ( std::string const& source, std::size_t line, info const& w)
      {
        using boost::spirit::basic_info_walker;

        std::ostringstream oss;
        oss << "(exception \"" << source << "\" ";

        if ( line == -1 )
          oss << -1;
        else
          oss << line;

        oss << " '(expected_component (";

        print_info < std::ostringstream > pr ( oss );
        basic_info_walker < print_info < std::ostringstream > > walker ( pr, w.tag, 0 );

        boost::apply_visitor ( walker, w.value );

        oss << ")))";

        msg = oss.str();
      }

      virtual ~expected_component() throw() {}

      virtual char const* what() const throw()
      {
        return msg.c_str(); 
      }
    }; 

    template<typename Iterator>
      struct error_handler
      {
        template<typename, typename, typename, typename >
          struct result
          {
            typedef void type;
          };

        error_handler ( ) {}

        void operator() (Iterator first, Iterator last, Iterator err_pos, info const& what ) const
        {
          using boost::spirit::get_line;
          Iterator eol = err_pos;
          std::size_t line = get_line (err_pos);
        }
      };

    template<typename Iterator>
      struct whitespace : qi::grammar < Iterator > 
    {
      qi::rule<Iterator> start;

      whitespace() : whitespace::base_type ( start )
      {
        using standard::space;
        using standard::char_;
        using qi::eol;

        start = space | ( ';' >> *(char_ - eol) >> eol ); 
      }

    };


    template<typename Iterator, typename Evaluator, typename ErrorHandler = error_handler<Iterator> >
    struct parser : qi::grammar < Iterator, utree::list_type(), whitespace<Iterator> >
    {
      qi::rule<Iterator, utree::list_type(), whitespace < Iterator > > start;
      qi::rule<Iterator, utree(), whitespace < Iterator > > numeral, sexpr;
      qi::rule<Iterator, boost::spirit::utf8_symbol_type(), whitespace < Iterator > > command_name;
      qi::rule<Iterator, boost::spirit::utf8_string_type(), whitespace < Iterator > > symbol;
      qi::rule<Iterator, utree::list_type(), whitespace < Iterator> > command;
      qi::rule<Iterator > end_of_word;  

      //      qi::rule<Iterator , utree()                           , whitespace < Iterator > > spec_constant;
      //      qi::rule<Iterator , boost::spirit::utf8_string(), whitespace < Iterator > > symbol;
      //      qi::rule<Iterator , boost::spirit::utf8_string(), whitespace < Iterator > > keyword;
      //      qi::rule<Iterator , boost::spirit::utf8_string(), whitespace < Iterator > > identifier;
      //      qi::rule<Iterator , utree::list_type()                           , whitespace < Iterator > > command;
      //      qi::rule<Iterator , utree::list_type()                , whitespace < Iterator > > script;
      //      qi::rule<Iterator , utree::list_type()                , whitespace < Iterator > > spec_expr;
      //      qi::rule<Iterator , utree::list_type()                           , whitespace < Iterator > > attribute      , sort;
      //      qi::rule<Iterator , utree()                           , whitespace < Iterator > > numeral        , decimal , hexadecimal , binary , string;
      //
      phoenix::function<ErrorHandler> const error;
      phoenix::function<Evaluator> const evaluate;

      parser ( Evaluator& evaluator ) : parser::base_type ( start ), evaluate ( evaluator ), error(ErrorHandler()), evaluator ( evaluator )
      {
        using standard::char_;
        using qi::unused_type;
        using qi::lexeme;
        using qi::hex;
        using qi::int_;
        using qi::oct;
        using qi::no_case;
        using qi::real_parser;
        using qi::uint_parser;
        using qi::bool_parser;
        using qi::on_error;
        using qi::fail;
        using qi::int_;
        using qi::lit;
        using qi::_val;
        using qi::_1;
        using qi::_2;
        using qi::_3;
        using qi::_4;
        using ascii::digit;
        using ascii::graph;
        using ascii::alpha;
        using qi::debug;

        start %= *( command ); // [ evaluate ( _val ) ] );

        command %= '(' >> command_name >> *sexpr >> ')';

        sexpr %= '(' >> *sexpr >> ')' | symbol | numeral;

        symbol %= lexeme [ +(qi::char_ -end_of_word ) ];

        numeral %= qi::uint_;

        command_name %= lexeme [ +(char_ - end_of_word ) ];

        end_of_word %= qi::space | char_(")");
        
        start.name ( "start" );
        command.name ( "command" ) ;
        sexpr.name ("s-expr" );
        symbol.name ( "symbol" );
        numeral.name ( "numeral" );
        command_name.name ( "command_name" );

#if 0
        debug ( start);
        debug ( command );
        debug ( sexpr );
        debug ( symbol );
        debug ( numeral );
        debug ( command_name ); 
#endif
      }
      
      Evaluator& evaluator;
    }; 

    template<typename Evaluator>
      class SMT2Parser
      {
        public:
          SMT2Parser ( boost::spirit::utree::list_type& utree, Evaluator& evaluator  ) : 
            ast ( utree )
          , evaluator ( evaluator )
        {

        }

          bool parse ( std::istream& instream, boost::spirit::utree::list_type& ast )
          {
            if ( !instream.good() )
            {
              return false; 
            }

            instream.unsetf ( std::ios::skipws );

            spirit::istream_iterator begin(instream);
            spirit::istream_iterator end;

            parser<spirit::istream_iterator, Evaluator> p ( evaluator );
            whitespace<spirit::istream_iterator> ws;

            bool r = phrase_parse ( begin, end, p, ws, ast );

            if ( !r )
            {
              std::cout << "Not r " << std::endl;
            }

            if ( begin != end )
            {
              std::cout << "begin != end" << std::endl;
            }

            if ( r && begin == end )
            {
              return true;
            }
            else
            {
              std::cerr << "Parsing failed." << std::endl;
              std::cout << "Stop at:" << std::string ( begin, end ) << std::endl; 
              return false; 
            }

            return r;

          }

        private:
          boost::spirit::utree::list_type& ast;
          Evaluator&                       evaluator;
      };
  }
}
