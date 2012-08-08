#pragma once

#include "../API/Options.hpp"

#include <boost/shared_ptr.hpp>

#include <map>

namespace metaSMT {
  struct Options;

  namespace option {
    struct NOPCommand {
      template < typename SolverType, typename T1 >
      static void action( SolverType const &, T1 const & ) {
        /* ignore command */
      }

      template < typename SolverType, typename T1, typename T2 >
      static void action( SolverType const &, T1 const &, T2 const & ) {
        /* ignore command */
      }

      template < typename SolverType, typename T1, typename T2, typename T3 >
      static void action( SolverType const &, T1 const &, T2 const &, T3 const & ) {
        /* ignore command */
      }
    }; // NOPCommand

    struct SetupOptionMapCommand {
      template < typename SolverType >
      static void action( SolverType &ctx, Options const &opt ) {
        ctx.command( setup_option_map_cmd(), opt );
      }
    }; // SetupOptionMapCommand

    struct SetOptionCommand {
      template < typename SolverType >
      static void action( SolverType &ctx, Options const &opt,
                          std::string const &key, std::string const &value ) {
        ctx.command( set_option_cmd(), opt, key, value );
      }
    }; // SetOptionCommand
  } // option

  struct Options {
    typedef std::map< std::string, std::string > Map;
    typedef boost::shared_ptr< Map > SharedMap;

    Options()
      : map( new Map() )
    {}

    Options(Map const &map)
      : map( new Map(map) )
    {}

    void set(std::string const &key, std::string const &value) {
      assert( map != 0 );
      (*map)[ key ] = value;
    }

    std::string get( std::string const &key ) const {
      assert( map != 0 );
      Map::const_iterator it = map->find( key );
      if ( it != map->end() ) {
        return it->second;
      }

      // Option has not been set.
      assert(false && "Could not determine value in map");
      throw std::exception();
    }

    std::string get( std::string const &key, std::string const &default_value ) const {
      assert( map != 0 );
      Map::const_iterator it = map->find( key );
      if ( it != map->end() ) {
        return it->second;
      }

      return default_value;
    }

    SharedMap map;
  }; // Options
}
