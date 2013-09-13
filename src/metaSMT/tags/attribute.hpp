#pragma once

namespace metaSMT {
  namespace attr {
    struct ignore {};

    struct constant {};
    struct unary {};
    struct binary {};
    struct ternary {};

    //@ nary attributes: see SMT-LIB2 Core theory
    struct right_assoc {};
    struct left_assoc {};
    struct chainable {};
    struct pairwise {};

    // special attribute for cardinality
    struct nary {};
  } // attr
} // metaSMT

