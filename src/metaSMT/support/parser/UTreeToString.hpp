#pragma once
#include <boost/spirit/include/support_utree.hpp>
#include <sstream>
#include <string>

namespace metaSMT {
  namespace evaluator {
    inline std::string utreeToString(boost::spirit::utree const tree) {
      std::stringstream ss;
      ss << tree;
      std::string output = ss.str();

      std::size_t found = output.find("\"");
      while (found != output.npos) {
        output.erase(found, 1);
        found = output.find("\"");
      }
      found = output.find(" ");
      while (found != output.npos) {
        output.erase(found, 1);
        found = output.find(" ");
      }

      if ( output == "(" || output == ")" ) {
        return output;
      }

      found = output.find("(");
      while (found != output.npos) {
        output.erase(found, 1);
        found = output.find("(");
      }
      found = output.find(")");
      while (found != output.npos) {
        output.erase(found, 1);
        found = output.find(")");
      }
      return output;
    }
  } // evaluator
} // metaSMT
