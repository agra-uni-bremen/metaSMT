#pragma once
#include <map>
#include <string>
#include <cstdio>
#include <boost/proto/proto.hpp>

namespace metaSMT {
  namespace support {
    struct simple_symbol_table {
      static std::map<unsigned, std::string> map_;

      std::string operator()(unsigned id) const {
        std::map<unsigned, std::string>::const_iterator it = map_.find(id);
        if ( it == map_.end() ) {
          // assert( false && "Invalid read in symbol table" );
          char buf[64];
          sprintf(buf, "var_%u", id);
          return buf;
        }
        return it->second;
      }

      template < typename T >
      void insert(T const &t, std::string const &name) {
        map_.insert(std::make_pair(boost::proto::value(t).id, name));
      }

      std::size_t size() const {
        return map_.size();
      }
    }; // simple_symbol_table
  } // support
}
