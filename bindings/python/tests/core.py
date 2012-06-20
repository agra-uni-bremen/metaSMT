#!/usr/bin/python
import inspect
import random
import sys
import unittest

sys.path.insert( 0, sys.path[0] + '/..' )

from metasmt.core import *

def skipIfNoSolver(obj):
  if obj.solver is not None:
      return lambda func: func
  return unittest.skip("solver is unavailable")

class LogicTest( object ):
    solver = None

    def test_variable( self ):
        p = new_variable()
        solver = self.solver()
        solver.solve()

    def check_with_solver( self, solver, metasmt_function, specification ):
        vars = tuple( new_variables( len( inspect.getargspec( metasmt_function ).args ) ) )

        solver.assertion( metasmt_function( *vars ) )
        self.assertTrue( solver.solve() )
        self.assertTrue( specification( *tuple( map( solver.__getitem__, vars ) ) ) )

    def check( self, metasmt_function, specification ):
        self.check_with_solver( self.solver(), metasmt_function, specification )

    def test_not( self ):
        self.check( logic_not, lambda a: not a )

    def test_equal( self ):
        self.check( logic_equal, lambda a, b: a == b )

    def test_nequal( self ):
        self.check( logic_nequal, lambda a, b: a != b )

    def test_implies( self ):
        self.check( logic_implies, lambda a, b: a <= b )

    def test_and( self ):
        self.check( logic_and, lambda a, b: a and b )

    def test_nand( self ):
        self.check( logic_nand, lambda a, b: not( a and b ) )

    def test_or( self ):
        self.check( logic_or, lambda a, b: a or b )

    def test_nor( self ):
        self.check( logic_nor, lambda a, b: not( a or b ) )

    def test_xor( self ):
        self.check( logic_xor, lambda a, b: a != b )

    def test_xnor( self ):
        self.check( logic_xnor, lambda a, b: a == b )

    def test_ite( self ):
        self.check( logic_ite, lambda a, b, c: ( a and b ) or ( not a and c ) )


def invert( v, bitwidth = 32 ):
    return v ^ ( ( 1 << bitwidth ) - 1 )

def twoscomp( v, bitwidth = 32 ):
    if v & (1 << ( bitwidth - 1 ) ) == 0:
        return v
    else:
        return -( invert( v - ( 1 << ( bitwidth - 1 ) ), bitwidth - 1 ) + 1 )

class BitvectorTest( object ):
    solver = None

    def check_with_solver( self, solver, metasmt_function, specification, bv = 32, rbv = 32, returns_bool = False, tbv = 32 ):
        vars = new_bitvectors( bv, len( inspect.getargspec( metasmt_function ).args ) )
        v = random.randint( 0, 2**rbv - 1 )

        solver = boolector_solver()
        if returns_bool:
            solver.assertion( metasmt_function( *vars ) )
        else:
            solver.assertion( reduce( logic_and, [ logic_nequal( var, bv_uint[bv]( 0 ) ) for var in vars ], True ) )
            solver.assertion( logic_equal( metasmt_function( *vars ), bv_uint[tbv]( v ) ) )
        self.assertTrue( solver.solve() )
        if specification:
            if returns_bool:
                self.assertTrue( specification( *tuple( map( solver.__getitem__, vars ) ) ) )
            else:
                self.assertTrue( specification( *tuple( map( solver.__getitem__, vars ) ) ) == v )

    def check( self, metasmt_function, specification, bv = 32, rbv = 32, returns_bool = False, tbv = 32 ):
        self.check_with_solver( self.solver(), metasmt_function, specification, bv, rbv, returns_bool, tbv )

    def testConstants( self ):
        solver = self.solver()
        a = new_bitvector( 32 )
        b = new_bitvector( 32 )
        c = new_bitvector( 32 )
        d = new_bitvector( 32 )

        solver.assertion( logic_equal( a, bv_uint[32]( 10 ) ) )
        solver.assertion( logic_equal( b, bv_sint[32]( -10 ) ) )
        solver.assertion( logic_equal( c, bv_bin( "00000000000000000000000000001010" ) ) )
        solver.assertion( logic_equal( d, bv_hex( "0000000A" ) ) )

        self.assertTrue( solver.solve() )
        self.assertTrue( solver[a] == -twoscomp( solver[b] ) )
        self.assertTrue( solver[c] == solver[d] )

    def testBVNot( self ):
        self.check( bv_not, lambda a: a ^ 2**32-1 )

    def testBVNeg( self ):
        self.check( bv_neg, lambda a: -twoscomp( a, 32 ), rbv = 31 )

    def testBVAnd( self ):
        self.check( bv_and, lambda a, b: a & b )

    def testBVNand( self ):
        self.check( bv_nand, lambda a, b: invert( a & b ) )

    def testBVOr( self ):
        self.check( bv_or, lambda a, b: a | b )

    def testBVNor( self ):
        self.check( bv_nor, lambda a, b: invert( a | b ) )

    def testBVXor( self ):
        self.check( bv_xor, lambda a, b: a ^ b )

    def testBVXnor( self ):
        self.check( bv_xnor, lambda a, b: invert( a ^ b ) )

    def testBVAdd( self ):
        self.check( bv_add, lambda a, b: ( a + b ) % 2**32 )

    def testBVMul( self ):
        self.check( bv_mul, lambda a, b: ( a * b ) % 2**32 )

    def testBVSub( self ):
        self.check( bv_sub, lambda a, b: ( a - b ) % 2**32 )

    def testBVSdiv( self ):
        self.check( bv_sdiv, None )

    def testBVSrem( self ):
        self.check( bv_srem, None )

    def testBVUdiv( self ):
        self.check( bv_udiv, lambda a, b: ( a / b ) )

    def testBVUrem( self ):
        self.check( bv_urem, lambda a, b: ( a % b ) )

    def testBVShl( self ):
        self.check( bv_shl, None )

    def testBVShr( self ):
        self.check( bv_shr, None )

    def testBVAshr( self ):
        self.check( bv_shr, None )

    def testBVComp( self ):
        self.check( bv_comp, lambda a, b: a == b, returns_bool = True )

    def testBVSlt( self ):
        self.check( bv_slt, lambda a, b: twoscomp( a ) < twoscomp( b ), returns_bool = True )

    def testBVSgt( self ):
        self.check( bv_sgt, lambda a, b: twoscomp( a ) > twoscomp( b ), returns_bool = True )

    def testBVSle( self ):
        self.check( bv_sle, lambda a, b: twoscomp( a ) <= twoscomp( b ), returns_bool = True )

    def testBVSge( self ):
        self.check( bv_sge, lambda a, b: twoscomp( a ) >= twoscomp( b ), returns_bool = True )

    def testBVUlt( self ):
        self.check( bv_ult, lambda a, b: a < b, returns_bool = True )

    def testBVUgt( self ):
        self.check( bv_ugt, lambda a, b: a > b, returns_bool = True )

    def testBVUle( self ):
        self.check( bv_ule, lambda a, b: a <= b, returns_bool = True )

    def testBVUge( self ):
        self.check( bv_uge, lambda a, b: a >= b, returns_bool = True )

    def testConcat( self ):
        self.check( concat, lambda a, b: ( a << 16 ) + b, bv = 16 )

    def testExtract( self ):
        solver = self.solver()
        a = new_bitvector( 32 )
        solver.assertion( logic_equal( a, bv_uint[32]( random.randint( 0, 2**32 - 1 ) ) ) )
        solver.assertion( logic_equal( a, reduce( concat, [ extract( i, i, a ) for i in ( range( 32 ) ) ] ) ) )
        self.assertTrue( solver.solve() )

    def testZeroExtend( self ):
        solver = self.solver()
        a = new_bitvector( 16 )
        solver.assertion( logic_implies( logic_equal( concat( a, a ), zero_extend( 16, a ) ),
                                         logic_equal( a, bv_uint[16]( 0 ) ) ) )
        self.assertTrue( solver.solve() )

    def testSignExtend( self ):
        solver = self.solver()
        a = new_bitvector( 16 )
        solver.assertion( logic_implies( logic_equal( concat( a, a ), sign_extend( 16, a ) ),
                                         logic_equal( a, bv_uint[16]( 0 ) ) ) )
        self.assertTrue( solver.solve() )


for name, solver in available_solvers().items():
  logic_name = 'LogicTest_'+name
  bitvec_name = 'BitvectorTest_'+name
  solver_fun = lambda self: solver()
  globals()[logic_name] = type(logic_name, (LogicTest, unittest.TestCase), dict(solver=solver_fun ))
  globals()[bitvec_name] = type('BitvectorTest_'+name, (BitvectorTest, unittest.TestCase), dict(solver=solver_fun))



if __name__ == "__main__":
    random.seed()
    unittest.main()

