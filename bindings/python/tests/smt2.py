#!/usr/bin/python
import os, sys
import unittest

pwd = sys.path[0]
sys.path.insert( 0, pwd + '/..' )

#os.environ['PATH'] = "%s/../../../deps/Z3-2.19/bin:%s" % ( pwd, os.environ['PATH'] )

from metasmt.core import *
from metasmt.operators import *
from metasmt.smt2 import *

def delete_tmp_files():
    for f in [ 'meta.%s' % f for f in [ 'smt2', 'sol' ]]:
        if os.path.exists( f ):
            os.unlink( f )

def skipIfNoSMT2(obj):
  if 'smt2' in available_solvers():
      return lambda func: func
  return unittest.skip("smt2 solver is unavailable")


@skipIfNoSMT2
class SMT2Test( unittest.TestCase ):
    def test_solver( self ):
        delete_tmp_files()

        a, b, c = new_bitvectors( 32, 3 )

        s = smt2_solver()
        s &= ( a == ( b & c ) )
        s.solve()

        delete_tmp_files()

    def test_symbol_table( self ):
        delete_tmp_files()

        a, b, c = new_bitvectors( 32, 3 )

        s = smt2_solver()

        s.symbol( a, "a" )
        s.symbol( b, "b" )
        s.symbol( c, "c" )
        s.install_symbol_table()

        s &= ( a == ( b & c ) )
        s.solve()

        self.assertEqual( len( filter( lambda s: s == '(assert (= a (bvand b c)))', map( str.strip, open( 'meta.smt2', 'r' ).readlines() ) ) ), 1 )

        delete_tmp_files()

    def test_symbol_table_with_vars( self ):
        delete_tmp_files()

        a, b, c = new_variables( 3 )

        s = smt2_solver()

        s.symbol( a, "a" )
        s.symbol( b, "b" )
        s.symbol( c, "c" )
        s.install_symbol_table()

        s &= ( a == ( b & c ) )
        s.solve()

        self.assertEqual( len( filter( lambda s: s == '(assert (= a (and b c)))', map( str.strip, open( 'meta.smt2', 'r' ).readlines() ) ) ), 1 )

        delete_tmp_files()

if __name__ == "__main__":
    unittest.main()

