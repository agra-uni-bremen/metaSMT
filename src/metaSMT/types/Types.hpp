#pragma once

#include "Boolean.hpp"
#include "BitVector.hpp"
#include "Array.hpp"
#include <boost/variant/variant.hpp>

namespace metaSMT {
  namespace type {
    typedef boost::variant<Boolean, BitVector, type::Array> any_type;
  }
}
