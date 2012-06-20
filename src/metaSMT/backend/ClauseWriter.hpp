#pragma once

#include "../tags/SAT.hpp"
#include "../result_wrapper.hpp"
#include "SAT/model_parser.hpp"
#include "../support/GoTmp.hpp"


#include <vector>
#include <exception>
#include <fstream>
#include <iostream>
#include <cstdio>

#include <boost/foreach.hpp>
#include <boost/format.hpp>
#include <boost/optional.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/algorithm/string/classification.hpp>
#include <boost/assign/std/vector.hpp>
#include <boost/lambda/lambda.hpp>
#include <boost/spirit/home/support/iterators/istream_iterator.hpp>
 
namespace metaSMT {
  namespace solver {
    using namespace boost::assign; 

    namespace executable {
      struct Glucoser // performs extended resolution 
      {
        static boost::optional < bool > execute ( std::string const& dimacsFile, std::string const& log, std::string const& err)
        {
          std::string cmd;
          char* env;
          if( (env = getenv("GLOCUSER_EXECUTABLE")) ) {
            cmd = env;
          } else {
            cmd = "glucoser";
          }
          std::string call = boost::str ( boost::format ( "%s %s  %s &> %s" ) % cmd % dimacsFile % log % err ) ;
          std::cout << call << std::endl;
          int returnValue = system ( call.c_str() ); 
          int exitStatus = WEXITSTATUS ( returnValue ); 

          if ( returnValue < 0 )
            return boost::optional < bool > (); 

          return boost::optional < bool > ( exitStatus == 10 );  // 10 for satisfiable, 20 for unsatisfiable 
        }
      }; 

      struct MiniSAT
      {
        static boost::optional < bool > execute ( std::string const& dimacsFile, std::string const& log, std::string const& err)
        {
          std::string cmd;
          char* env;
          if( (env = getenv("MiniSat_EXECUTABLE")) ) {
            cmd = env;
          } else {
            cmd = "minisat";
          }
          int returnValue = system ( boost::str ( boost::format ( "%s %s  %s &> %s" ) % cmd % dimacsFile % log % err ).c_str() ); 
          int exitStatus = WEXITSTATUS ( returnValue ); 

          if ( returnValue < 0 )
            return boost::optional < bool > (); 

          return boost::optional < bool > ( exitStatus == 10 );  // 10 for satisfiable, 20 for unsatisfiable 
        }
      }; 

      struct PicoSAT
      {
        static boost::optional < bool > execute ( std::string const& dimacsFile, std::string const& log, std::string const& err)
        {
          std::string cmd;
          char* env;
          if( (env = getenv("PicoSAT_EXECUTABLE")) ) {
            cmd = env;
          } else {
            cmd = "picosat";
          }
          int returnValue = system ( boost::str ( boost::format ( "%s %s > %s 2> %s" ) % cmd % dimacsFile % log % err ).c_str() ); 
          int exitStatus = WEXITSTATUS ( returnValue ); 

          if ( returnValue < 0 )
            return boost::optional < bool > (); 

          bool sat = exitStatus == 10;

          return boost::optional < bool > ( sat  );  // 10 for satisfiable 
        }
      };

      struct Plingeling
      {
        static boost::optional < bool > execute ( std::string const& dimacsFile, std::string const& log, std::string const& err)
        {
          int returnValue = system ( boost::str ( boost::format ( "plingeling -v %s > %s 2> %s" ) % dimacsFile % log % err).c_str() ); 
          int exitStatus = WEXITSTATUS ( returnValue ); 

          if ( returnValue < 0 )
            return boost::optional < bool > (); 

          bool sat = exitStatus == 10;

          //std::cout << "SAT: " << sat << std::endl;

          return boost::optional < bool > ( sat  );  // 10 for satisfiable 
        }
      };

      struct PrecoSAT
      {
        static boost::optional < bool > execute ( std::string const& dimacsFile, std::string const& log, std::string const& err)
        {
          int returnValue = system ( boost::str ( boost::format ( "precosat -v %s > %s " ) % dimacsFile % err).c_str() ); 
          int exitStatus = WEXITSTATUS ( returnValue ); 

          if ( returnValue < 0 )
            return boost::optional < bool > (); 

          bool sat = exitStatus == 10;

          //std::cout << "SAT: " << sat << std::endl;

          return boost::optional < bool > ( sat  );  // 10 for satisfiable 
        }
      };
    }


    template<typename Exec>
      struct dimacs_solver
      {
        dimacs_solver ( std::vector < unsigned >& model ) : model ( model )
        {
        }

        void readModel ( std::string const& log ) 
        {
          // open file, disable skipping of whitespace
          std::ifstream in(log.c_str());
          in.unsetf(std::ios::skipws);

          // wrap istream into iterator
          boost::spirit::istream_iterator begin(in);
          boost::spirit::istream_iterator end;
          SAT::model_grammar<boost::spirit::istream_iterator> p;

          SAT::result_tuple result;
          // use iterator to parse file data
          bool match = boost::spirit::qi::parse(begin, end, p, result);
          assert ( match );

          BOOST_FOREACH ( int val, result.get<1>() )
          {
            if ( val == 0 ) continue;
            unsigned position = abs ( val );
            unsigned X = val < 0 ? 0 : 1;
            if (position >= model.size()) {
              std::cout << model.size() << " " << position << std::endl;
            }
            assert(model.size() > position);
            model[position] = X;
          }

        }

        boost::optional < bool > solve ( std::string const& filename )
        {
          std::string log = boost::str( boost::format("solver-%d.log") % getpid());
          std::string err = boost::str( boost::format("solver-%d.err") % getpid());

          boost::optional < bool > result = Exec::execute ( filename, log, err ); 

          bool returnValue = false;
          if ( result )
          {
            //std::cout << "SAT? " << *result << std::endl;
            if ( *result )
            {
              readModel ( log );
              returnValue = true;
            }
            else
              returnValue = false;
          }

          std::remove( log.c_str() );
          std::remove( err.c_str() );

          return returnValue;
        }

        private:
        std::vector < unsigned >& model;
      }; 

    template<typename Solver>
      class ClauseWriter
      {
        public:
          typedef std::vector < int > clause_vec;
          typedef std::vector < clause_vec > clause_db; 

        public:
          ClauseWriter () : vars (0)
        {
        }

          int toLit ( SAT::tag::lit_tag lit )
          {
            int l = lit.id; 

            if ( unsigned (abs ( l ) ) > vars )
              vars = abs ( l ); 

            return l;
          }

          void clause ( std::vector < SAT::tag::lit_tag > const& fromClause )
          {
            clause_vec cls;
            BOOST_FOREACH ( SAT::tag::lit_tag const& lit, fromClause )
              cls += toLit ( lit );
            db += cls;
          }

          void assertion ( SAT::tag::lit_tag lit )
          {
            clause_vec cls;
            cls += toLit ( lit ); 
            db.push_back ( cls ); 
          }

          void assumption ( SAT::tag::lit_tag lit )
          {
            clause_vec cls;
            cls += toLit ( lit ); 
            assumptions.push_back ( cls ); 
          }

          void write_header ( std::ostream& stream )
          {
            stream << "p cnf " << vars << " " << db.size() + assumptions.size() << std::endl;
          }

          void write_cnf ( std::string const& filename )
          {
            std::ofstream cnf ( filename.c_str() ) ;
            write_header ( cnf ); 

            BOOST_FOREACH ( clause_vec const& cls, db )
            {
              std::for_each (cls.begin(), cls.end(),
                  cnf << boost::lambda::free1 << " "); 
              cnf << "0" << std::endl;
            }

            BOOST_FOREACH ( clause_vec const& cls, assumptions )
            {
              std::for_each (cls.begin(), cls.end(),
                  cnf << boost::lambda::free1 << " "); 
              cnf << "0" << std::endl;
            }
          }

          bool solve ( )
          {
            // // GoTmp working_directory;
            std::string name = boost::str( boost::format("clause-writer-%d.cnf") % getpid());
            write_cnf ( name ); 

            //system ("cnf2aig clause-writer.cnf clause-writer.aig");
            //system ("optimize_aig.sh clause-writer.aig ");
            //system ("aigtocnf clause-writer.aig clause-writer.cnf");

            assumptions.clear(); 

            model.resize ( vars+1, 0 ); 

            Solver solver ( model );
            boost::optional < bool > result = solver.solve ( name ); 

            assert ( result );

            std::remove(name.c_str());

            if ( *result == false ) return false;

            return true;
          }

          result_wrapper read_value ( SAT::tag::lit_tag lit ) 
          {
            assert ( !model.empty() ); 
            assert ( int(model.size()) > toLit ( lit ) ); 

            switch ( model[ abs ( toLit ( lit ) ) ] )
            {
              case 1:
                return result_wrapper ( '1' );
              case 0:
                return result_wrapper ( '0' );
              default:
                assert ( false ); 
                return result_wrapper ( 'X' );

            }
          }

        private:
          clause_db     db; 
          clause_db     assumptions;
          unsigned      vars;
          std::vector < unsigned > model; 
      };
  } /* solver */
} /* metaSMT */
// vim: ts=2 sw=2 et
