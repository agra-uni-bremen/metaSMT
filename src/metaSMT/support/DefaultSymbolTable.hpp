#pragma once
#include <cstdio>
#include <string>

namespace metaSMT {
  namespace support {
    inline std::string default_symbol_table(unsigned id) {
      char buf[64];
      sprintf(buf, "var_%u", id);
      return buf;
    }
  } // support
} // metaSMT

