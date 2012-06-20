#!/usr/bin/python
import sys
import unittest

sys.path.insert( 0, sys.path[0] + '/..' )

from metasmt.core import *
from metasmt.operators import *
from metasmt.support import *

class SupportTest( object ):
    def testOneHot( self ):
        vars = new_variables( 10 )
        bv = new_bitvector( 10 )

        solver = self.solver()
        solver &= one_hot( vars )
        solver &= one_hot( bv, 10 )
        self.assertTrue( solver.solve() )
        self.assertEqual( len( [ v for v in map( solver.read_value, vars ) if v ] ), 1 )
        self.assertEqual( len( [ v for v in [ 2**i & solver.read_value( bv ) != 0 for i in range( 10 ) ] if v ] ), 1 )

    def testCardinality( self ):
        vgeq = new_variables( 10 )
        vlt  = new_variables( 10 )
        vleq = new_variables( 10 )
        vgt  = new_variables( 10 )
        veq  = new_variables( 10 )

        solver = self.solver()
        solver &= cardinality_geq( vgeq, 5 )
        solver &= cardinality_lt( vlt, 5 )
        solver &= cardinality_leq( vleq, 5 )
        solver &= cardinality_gt( vgt, 5 )
        solver &= cardinality_eq( veq, 5 )
        self.assertTrue( solver.solve() )
        self.assertGreaterEqual( len( [ v for v in map( solver.read_value, vgeq ) if v ] ), 5 )
        self.assertLess( len( [ v for v in map( solver.read_value, vlt ) if v ] ), 5 )
        self.assertLessEqual( len( [ v for v in map( solver.read_value, vleq ) if v ] ), 5 )
        self.assertGreater( len( [ v for v in map( solver.read_value, vgt ) if v ] ), 5 )
        self.assertEqual( len( [ v for v in map( solver.read_value, veq ) if v ] ), 5 )

for name, solver in available_solvers().items():
  test_name = 'SupportTest_'+name
  solver_fun = lambda self: solver()
  globals()[test_name] = type(test_name, (SupportTest, unittest.TestCase), dict(solver=solver_fun ))

if __name__ == "__main__":
    unittest.main()

