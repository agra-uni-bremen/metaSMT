from metasmt.core import *

def _solver_install_symbol_table( self ):
    assert hasattr( self, 'symbol_table' )
    self.set_symbol_table( self.symbol_table )

def _solver_symbol( self, var, name ):
    if not hasattr( self, 'symbol_table' ):
        self.symbol_table = smt2_symbol_table()

    self.symbol_table.insert( var, name )

solver.install_symbol_table = _solver_install_symbol_table
solver.symbol = _solver_symbol
