from metasmt.core import *
from metasmt.operators import *

import math

def _adjust( ps, width ):
    if width == None:
        width = len( ps )
    else:
        ps = [ ps[i] == True for i in range( width ) ]
    assert( width > 0 )
    return ( ps, width )

def one_hot( ps, width = None ):
    # Parameters
    ps, width = _adjust( ps, width )

    # Encoding
    if width == 1:
        return ps[0] == True

    zero_rail = ps[0]
    one_rail = -ps[0]

    for u in range( 1, width - 1 ):
        zero_rail = logic_ite( ps[u], one_rail, zero_rail )
        one_rail = logic_ite( ps[u], False, one_rail )

    return logic_ite( ps[width - 1], one_rail, zero_rail )

def cardinality_geq( ps, k, width = None ):
    # Parameters
    ps, width = _adjust( ps, width )

    # Encoding
    if width < k:
        return False
    elif width == k:
        return reduce( logic_and, ps )
    elif k == 0:
        return True

    rails = [ [None] * k ] * 2

    for v in range( width - k + 1 ):
        for u in range( k ):
            if u == 0 and v == 0:
                rails[0][0] = ps[0]
            elif u == 0:
                rails[v % 2][0] = logic_ite( ps[v], True, rails[(v-1)%2][0] )
            elif v == 0:
                rails[0][u] = logic_ite( ps[u], rails[0][u-1], False )
            else:
                rails[v%2][u] = logic_ite( ps[u+v], rails[v%2][u-1], rails[(v-1)%2][u] )
    return rails[(width - k) % 2][k - 1]

def cardinality_lt( ps, k, width = None ):
    return logic_not( cardinality_geq( ps, k, width ) )

def cardinality_leq( ps, k, width = None ):
    return logic_not( cardinality_geq( ps, k + 1, width ) )

def cardinality_gt( ps, k, width = None ):
    return logic_not( cardinality_leq( ps, k, width ) )

def cardinality_eq( ps, k, width = None ):
    return cardinality_geq( ps, k, width ) & cardinality_leq( ps, k, width )

# Join a list of single bit expressions as vector
def bv_join( l ):
    def to_bv( c ):
        if c.type() == 0:
            return logic_ite( c, bit1, bit0 )
        else:
            return c
    return reduce( concat, reversed( map( to_bv, l ) ) )

# Counts the bits in a bit-vector in a very inefficient way
def bv_count( bv, width ):
    return reduce( bv_add, [ zero_extend( width - 1, bv[i] ) for i in range( width ) ], bv_uint[width]( 0 ) )


# Get bit-width for values
def bits_for_values( values ):
    return int( math.ceil( math.log( values ) / math.log( 2.0 ) ) )
