#pragma once
#include <map>
#include <string>
#include <boost/proto/proto.hpp>

namespace metaSMT {
  namespace support {
    struct simple_symbol_table {
      static std::map<unsigned, std::string> map_;

      std::string operator()(unsigned id) const {
        std::map<unsigned, std::string>::const_iterator it = map_.find(id);
        assert( it != map_.end() && "invalid read in symbol table");
        return it->second;
        // return map_[id];
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
