from metasmt_python import *

# Variables
def new_variables( num ):
    return [ new_variable() for _ in range( num ) ]

def new_bitvectors( bw, num ):
    return [ new_bitvector( bw ) for _ in range( num ) ]

# Terminals
class _bv_int_impl:
    def __init__( self, func ):
        self.func = func
    def __getitem__( self, bitwidth ):
        return lambda value: self.func( value, bitwidth )
    def __call__( self, value ):
      class _bv_int_impl_value:
          def __init__( self, func ):
              self.func = func
          def __getitem__( self, bitwidth ):
              return self.func( value, bitwidth )
      return _bv_int_impl_value( self.func )
bv_uint = _bv_int_impl( py_bv_uint )
bv_sint = _bv_int_impl( py_bv_sint )
def bv_bin( s ): return py_bv_bin( s )
def bv_hex( s ): return py_bv_hex( s )
bit0 = py_bv_bit0()
bit1 = py_bv_bit1()

# Logic Expressions
def to_logic_expression( expr ):
    if   type( expr ) == bool:      return py_logic_term( expr )
    elif type( expr ) == predicate: return py_logic_predicate( expr )
    elif type( expr ) == bitvector: return py_logic_bv( expr )
    elif type( expr ) == array:     return py_logic_array( expr )
    elif type( expr ) == str:
        if expr.startswith( 'x' ): return bv_hex( expr[1:] )
        else:                      return bv_bin( expr )
    elif hasattr( expr, 'to_logic_expression' ): return expr.to_logic_expression()
    else:                           return expr

# Logic Functions
def _logic_unary( f ): return lambda a: f( to_logic_expression( a ) )
def _logic_binary( f ): return lambda a, b: f( to_logic_expression( a ), to_logic_expression( b ) )
def _logic_ternary( f ): return lambda a, b, c: f( to_logic_expression( a ), to_logic_expression( b ), to_logic_expression( c ) )
def _logic_nary( f ):
	def fun(*args):
		return f( map(to_logic_expression, args) )
	return fun

_logic = { _logic_unary: ['not'],
           _logic_binary: ['equal', 'nequal', 'implies', 'nand', 'nor', 'xor', 'xnor'],
           _logic_ternary: ['ite'],
           _logic_nary: ['and', 'or'],
}

for ( w, fs ) in _logic.items():
    for f in fs:
        globals()["logic_%s" % f] = w( globals()["py_logic_%s" % f] )

# BitVector Functions
_bv = { _logic_unary: ['not', 'neg'],
        _logic_binary: ['and', 'nand', 'or', 'nor', 'xor', 'xnor', 'add', 'mul', 'sub', 'sdiv', 'srem', 'udiv', 'urem', 'shl', 'shr', 'ashr',
                        'comp', 'slt', 'sgt', 'sle', 'sge', 'ult', 'ugt', 'ule', 'uge'] }
for ( w, fs ) in _bv.items():
    for f in fs:
        globals()["bv_%s" % f] = w( globals()["py_bv_%s" % f] )

def array_store(array, index, value):
    return py_array_store(to_logic_expression(array), to_logic_expression(index), to_logic_expression(value))

def array_select(array, index):
    return py_array_select(to_logic_expression(array), to_logic_expression(index))

def concat( a, b ): return py_concat( to_logic_expression( a ), to_logic_expression( b ) )
def extract( _from, width, expr ): return py_extract( _from, width, to_logic_expression( expr ) )
def zero_extend( by, expr ): return py_zero_extend( by, to_logic_expression( expr ) )
def sign_extend( by, expr ): return py_sign_extend( by, to_logic_expression( expr ) )

# Solver
def _solver_assertion( solver, expression ):
    solver.py_assertion( to_logic_expression( expression ) )

def _solver_assumtion ( solver, expression ):
    solver.py_assumption ( to_logic_expression( expression ) )

solver.assertion = _solver_assertion
solver.assumption = _solver_assumtion

def available_solvers():
    return dict( [ ( "%s_solver" % s, globals()["%s_solver" % s] ) for s in (
        "sword","boolector",
        "z3",
        "cudd",
        "minisat",
        "minisat_aiger",
        "picosat",
        "glucoser_executable",
        "minisat_executable",
        "picosat_executable",
        "plingeling_executable",
        "precosat_executable",
        "smt2",
        "constraint",
	) if "%s_solver" % s in globals() ] )
