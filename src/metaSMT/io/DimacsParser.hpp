
#pragma once

#include <fstream>
#include <vector>
#include <set>

#include <boost/algorithm/string/trim.hpp>
#include <boost/assign/std/vector.hpp>
#include <boost/assign/std/set.hpp>
#include <boost/config/warning_disable.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/foreach.hpp>

#include "../API/AddClause.hpp"

#define foreach BOOST_FOREACH

namespace metaSMT
{
  namespace dimacs
  {
    template<typename Iterator>
    bool parse_dimacs_clause ( Iterator first, Iterator last, std::vector < int >& clause )
    {
      namespace qi = boost::spirit::qi;
      namespace ascii = boost::spirit::ascii;
      namespace phoenix = boost::phoenix;
       
      using namespace boost::assign;
      using qi::int_;
      using qi::phrase_parse;
      using qi::_1;
      using ascii::space;
      using phoenix::push_back;
      using phoenix::ref;

      bool r = phrase_parse ( first, last,
          ( 
           *( int_ [ push_back ( ref( clause ), _1 )] - int_(0) ) >> int_(0) 
          )
          ,
          space );

      if ( first != last )
        return false;
      return true;

    }

    template<typename Context>
    void addclause_to_context ( Context& ctx, std::vector < int > read_clause )
    {
      std::vector < SAT::tag::lit_tag > clause ( read_clause.size() );

      for ( unsigned i = 0; i < read_clause.size(); i++ )
      {
        clause[i].id = read_clause[i];
      }
      
      add_clause ( ctx, clause );
    }

    template<typename Context>
    static bool parse_dimacs ( std::ifstream& stream, Context& context, std::set < unsigned >& vars )
    {
      std::string line;
      unsigned n = 1;
      while ( std::getline ( stream, line ) )
      {
        boost::trim ( line );

        if (line.empty() || line[0] == 'p' || line[0] == 'c' ) continue;

        std::vector < int > clause;
        bool r = parse_dimacs_clause ( line.begin(), line.end(), clause );

        addclause_to_context ( context, clause );

        foreach ( int lit, clause )
        {
          vars.insert ( abs ( lit ) );
        }

        if (!r)
        {
          std::cerr << "Invalid Dimacs file at line " << n << "." << std::endl;
          return false;
        }
        n++;
      }

      return true;
    }
  }
}













