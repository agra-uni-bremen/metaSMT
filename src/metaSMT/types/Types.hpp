#pragma once

#include <boost/variant/variant.hpp>
#include "Boolean.hpp"
#include "BitVector.hpp"

namespace metaSMT {
  namespace type {
    typedef boost::variant<Boolean, BitVector> any_type;
  }
}
