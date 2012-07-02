from metasmt.core import *

import inspect

# Expressions
def install_operator( sym, types, functions ):
    # Process Types
    if types == '*':
        types = [ predicate, bitvector, logic_expression ]
    elif not isinstance( types, list ):
        types = [ types ]

    # Process Functions
    if not isinstance( functions, tuple ):
        functions = ( functions, functions )

    # Install the operator
    n = len( inspect.getargspec( functions[0] ).args )
    if n == 1:
        f = lambda a: functions[to_logic_expression( a ).type()]( a )
    elif n == 2:
        f = lambda a, b: functions[to_logic_expression( a ).type()]( a, b )
    elif n == 3:
        f = lambda a, b, c: functions[to_logic_expression( a ).type()]( a, b, c )

    for t in types:
        setattr( t, sym, f )

def member_extract(self, x):
    if isinstance( x, tuple ):
		return extract( x[0], x[1], self )
    else:
        return extract( x, x, self )

def install_extract( types ):
    # Process Types
    if types == '*':
        types = [ predicate, bitvector, logic_expression ]
    elif not isinstance( types, list ):
        types = [ types ]

    for t in types:
        setattr( t, '__getitem__', member_extract )

install_operator( '__neg__', '*', ( logic_not, bv_not ) )
install_operator( '__eq__', '*', logic_equal )
install_operator( '__ne__', '*', logic_nequal )
install_operator( '__and__', '*', ( logic_and, bv_and ) )
install_operator( '__or__', '*', ( logic_or, bv_or ) )
install_operator( '__xor__', '*', ( logic_xor, bv_xor ) )
install_operator( '__invert__', [ bitvector, logic_expression ], bv_neg )
install_operator( '__add__', [ bitvector, logic_expression ], bv_add )
install_operator( '__mul__', [ bitvector, logic_expression ], bv_mul )
install_operator( '__sub__', [ bitvector, logic_expression ], bv_sub )
install_operator( '__div__', [ bitvector, logic_expression ], bv_udiv )
install_operator( '__mod__', [ bitvector, logic_expression ], bv_urem )
install_operator( '__lshift__', [ bitvector, logic_expression ], bv_shl )
install_operator( '__rshift__', [ bitvector, logic_expression ], bv_shr )
install_operator( '__lt__', [ bitvector, logic_expression ], bv_ult )
install_operator( '__gt__', [ bitvector, logic_expression ], bv_ugt )
install_operator( '__le__', [ bitvector, logic_expression ], bv_ule )
install_operator( '__ge__', [ bitvector, logic_expression ], bv_uge )
install_operator( '__pow__', [ bitvector, logic_expression ], concat )

install_extract( [ bitvector, logic_expression ] )

# Solver
def _solver_iand( self, clause ):
    self.assertion( clause )
    return self
solver.__iand__ = _solver_iand
