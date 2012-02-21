#!/usr/bin/python
import inspect
import random
import sys
import unittest

sys.path.insert( 0, sys.path[0] + '/..' )

from metasmt.core import *
from metasmt.operators import *

class LogicTest( object ):
    def test_variable( self ):
        p = new_variable()
        solver = self.solver()
        solver.solve()

    def check_with_solver( self, solver, metasmt_function, specification ):
        vars = tuple( new_variables( len( inspect.getargspec( metasmt_function ).args ) ) )

        solver &= metasmt_function( *vars )
        self.assertTrue( solver.solve() )
        self.assertTrue( specification( *tuple( map( solver.__getitem__, vars ) ) ) )

    def check( self, metasmt_function, specification ):
        solver = self.solver()
        self.check_with_solver( solver, metasmt_function, specification )

    def test_not( self ):
        self.check( lambda a: -a, lambda a: not a )

    def test_equal( self ):
        self.check( lambda a, b: a == b, lambda a, b: a == b )

    def test_nequal( self ):
        self.check( lambda a, b: a != b, lambda a, b: a != b )

    def test_implies( self ):
        pass

    def test_and( self ):
        self.check( lambda a, b: a & b, lambda a, b: a and b )

    def test_nand( self ):
        pass

    def test_or( self ):
        self.check( lambda a, b: a | b, lambda a, b: a or b )

    def test_nor( self ):
        pass

    def test_xor( self ):
        self.check( lambda a, b: a ^ b, lambda a, b: a != b )

    def test_xnor( self ):
        pass

    def test_ite( self ):
        pass

def invert( v, bitwidth = 32 ):
    return v ^ ( ( 1 << bitwidth ) - 1 )

def twoscomp( v, bitwidth = 32 ):
    if v & (1 << ( bitwidth - 1 ) ) == 0:
        return v
    else:
        return -( invert( v - ( 1 << ( bitwidth - 1 ) ), bitwidth - 1 ) + 1 )

class BitvectorTest( object ):
    def check_with_solver( self, solver, metasmt_function, specification, bv = 32, rbv = 32, returns_bool = False, tbv = 32 ):
        vars = new_bitvectors( bv, len( inspect.getargspec( metasmt_function ).args ) )
        v = random.randint( 0, 2**rbv - 1 )

        solver = self.solver()
        if returns_bool:
            solver &= metasmt_function( *vars )
        else:
            solver &= reduce( logic_and, [ logic_nequal( var, bv_uint[bv]( 0 ) ) for var in vars ], True )
            solver &= logic_equal( metasmt_function( *vars ), bv_uint[tbv]( v ) )
        self.assertTrue( solver.solve() )
        if specification:
            if returns_bool:
                self.assertTrue( specification( *tuple( map( solver.__getitem__, vars ) ) ) )
            else:
                self.assertTrue( specification( *tuple( map( solver.__getitem__, vars ) ) ) == v )

    def check( self, metasmt_function, specification, bv = 32, rbv = 32, returns_bool = False, tbv = 32 ):
        solver = self.solver()
        self.check_with_solver( solver, metasmt_function, specification, bv, rbv, returns_bool, tbv )

    def testConstants( self ):
        solver = self.solver()
        a = new_bitvector( 32 )
        b = new_bitvector( 32 )
        c = new_bitvector( 32 )
        d = new_bitvector( 32 )

        solver &= a == bv_uint[32]( 10 )
        solver &= b == bv_sint[32]( -10 )
        solver &= c == "00000000000000000000000000001010"
        solver &= d == "x0000000A"

        self.assertTrue( solver.solve() )
        self.assertTrue( solver[a] == -twoscomp( solver[b] ) )
        self.assertTrue( solver[a] == solver[c] )
        self.assertTrue( solver[a] == solver[d] )

    def testBVNot( self ):
        self.check( lambda a: -a, lambda a: a ^ 2**32-1 )

    def testBVNeg( self ):
        self.check( lambda a: ~a, lambda a: -twoscomp( a, 32 ), rbv = 31 )

    def testBVAnd( self ):
        self.check( lambda a, b: a & b, lambda a, b: a & b )

    def testBVNand( self ):
        pass

    def testBVOr( self ):
        self.check( lambda a, b: ( a | b ), lambda a, b: a | b )

    def testBVNor( self ):
        pass

    def testBVXor( self ):
        self.check( lambda a, b: a ^ b, lambda a, b: a ^ b )

    def testBVXnor( self ):
        pass

    def testBVAdd( self ):
        self.check( lambda a, b: a + b, lambda a, b: ( a + b ) % 2**32 )

    def testBVMul( self ):
        self.check( lambda a, b: a * b, lambda a, b: ( a * b ) % 2**32 )

    def testBVSub( self ):
        self.check( lambda a, b: a - b, lambda a, b: ( a - b ) % 2**32 )

    def testBVSdiv( self ):
        pass

    def testBVSrem( self ):
        pass

    def testBVUdiv( self ):
        self.check( lambda a, b: a / b, lambda a, b: ( a / b ) )

    def testBVUrem( self ):
        self.check( lambda a, b: a % b, lambda a, b: ( a % b ) )

    def testBVShl( self ):
        self.check( lambda a, b: a << b, None )

    def testBVShr( self ):
        self.check( lambda a, b: a >> b, None )

    def testBVAshr( self ):
        pass

    def testBVComp( self ):
        pass

    def testBVSlt( self ):
        pass

    def testBVSgt( self ):
        pass

    def testBVSle( self ):
        pass

    def testBVSge( self ):
        pass

    def testBVUlt( self ):
        self.check( lambda a, b: a < b, lambda a, b: a < b, returns_bool = True )

    def testBVUgt( self ):
        self.check( lambda a, b: a > b, lambda a, b: a > b, returns_bool = True )

    def testBVUle( self ):
        self.check( lambda a, b: a <= b, lambda a, b: a <= b, returns_bool = True )

    def testBVUge( self ):
        self.check( lambda a, b: a >= b, lambda a, b: a >= b, returns_bool = True )

    def testConcat( self ):
        self.check( lambda a, b: a ** b, lambda a, b: ( a << 16 ) + b, bv = 16 )

    def testExtract( self ):
        solver = self.solver()
        a = new_bitvector( 32 )
        solver &= a == bv_uint[32]( random.randint( 0, 2**32 - 1 ) )
        solver &= a == reduce( concat, [ a[i] for i in reversed( range( 32 ) ) ] )
        self.assertTrue( solver.solve() )

    def testZeroExtend( self ):
        pass

    def testSignExtend( self ):
        pass

    def testAndPrecedence(self):
        solver = self.solver()
        a = new_bitvector(8);
        solver &=   bv_uint(1)[8] < a < bv_uint(8)[8]
        self.assertTrue( solver.solve() )
        v = solver[a]
        self.assertLess(1,v)
        self.assertLess(v,8)

        solver &=    bv_uint(1)[8] < a & a < bv_uint(8)[8]
        self.assertTrue( solver.solve() )
        v = solver[a]
        self.assertLess(1,v)
        self.assertLess(v,8)

        solver &=   a > bv_uint(1)[8]  &  a < bv_uint(8)[8]
        self.assertTrue( solver.solve() )
        v = solver[a]
        self.assertLess(1,v)
        self.assertLess(v,8)

        solver &=   (a > bv_uint(1)[8])  &  (bv_uint(8)[8] > a)
        self.assertTrue( solver.solve() )
        v = solver[a]
        self.assertLess(1,v)
        self.assertLess(v,8)

        # interpreted  as: a > (bv_uint(1)[8]  &  bv_uint(8)[8]) > a
        solver &=          a > bv_uint(1)[8]   &  bv_uint(8)[8]  > a
        self.assertFalse( solver.solve() )

# instanciate the tests for all available solvers
for name, solver in available_solvers().items():
  logic_name = 'LogicTest_'+name
  bitvec_name = 'BitvectorTest_'+name
  solver_fun = lambda self: solver()
  globals()[logic_name] = type(logic_name, (LogicTest, unittest.TestCase), dict(solver=solver_fun ))
  globals()[bitvec_name] = type('BitvectorTest_'+name, (BitvectorTest, unittest.TestCase), dict(solver=solver_fun))

def print_tests(test):
  if isinstance(test, unittest.suite.TestSuite):
    map(print_tests, test)
  else:
    print test

if __name__ == "__main__":
    random.seed()
    if len(sys.argv) == 2 and sys.argv[1] == '--discover':
      import os
      tests = unittest.defaultTestLoader.discover(os.path.dirname(__file__), pattern='*.py')
      print_tests(tests)
    else:
      unittest.main()

