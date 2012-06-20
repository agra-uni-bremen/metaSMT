#!/usr/bin/python
from metasmt.core import *
from metasmt.operators import *
import random

default_bitwidth = 24

def prime_test(number, solver=boolector_solver(), bitwidth=default_bitwidth):
  a = new_bitvector( bitwidth )
  b = new_bitvector( bitwidth )

  ext = lambda x: zero_extend( bitwidth, x)

  ## a*b=c (avoiding overflows)
  solver.assertion(
      logic_equal(
        bv_mul( ext(a), ext(b)),
        bv_uint(number)[2*bitwidth]
        )
      )
  solver.assertion( logic_nequal( a, bv_uint(1)[bitwidth]) )
  solver.assertion( logic_nequal( b, bv_uint(1)[bitwidth]) )

  if solver.solve():
    return (
        solver.read_value(a),
        solver.read_value(b),
        )
  else:
    return None

def prime_test_operators(number, solver=boolector_solver(), bitwidth=default_bitwidth):
  a = new_bitvector( bitwidth )
  b = new_bitvector( bitwidth )

  ext = lambda x: zero_extend( bitwidth, x)

  ## a*b=c (avoiding overflows)
  solver &= ext(a) * ext(b) == bv_uint(number)[2*bitwidth]
  solver &= a != bv_uint(1)[bitwidth]
  solver &= b != bv_uint(1)[bitwidth]
  solver &= a <= b

  if solver.solve():
    return ( solver[a], solver[b] )
  else:
    return None


def main():
  while True:
    rand = random.randint(2, 2**default_bitwidth-1)
    print "%8d" % rand,
    result = prime_test_operators( rand )
    if result is None:
      print "is prime"
      break;
    else:
      print "can be factorized into %8d * %8d" % result

if __name__ == '__main__':
  main()
