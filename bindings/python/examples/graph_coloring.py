#!/usr/bin/python
import random
import sys

sys.path.insert( 0, sys.path[0] + '/..' )
from metasmt.core import *
from metasmt.operators import *
from metasmt.support import *

import matplotlib.pyplot as plt
import networkx as nx

# Graph Coloring
def graph_coloring( G, num_colors,
                    solver = boolector_solver(),
                    colors = [ 'red', 'green', 'blue', 'yellow', 'orange', 'purple', 'orange', 'cyan', 'magenta' ]):

    # Bit-width of variables
    bw = bits_for_values( num_colors )

    # Create variables for each vertex
    vmap = dict( [ ( n, new_bitvector( bw ) ) for n in G.nodes() ] )

    # Color in range
    for b in vmap.values():
        solver &= ( b <= bv_uint[bw]( num_colors ) )

    # Different color for adjacent vertices
    for v, w in G.edges():
        solver &= vmap[v] != vmap[w]

    r = solver.solve()
    print r, solver
    if r:
        for n, b in vmap.items():
            G.node[n]['color'] = colors[solver[b]]
        return True
    else:
        return False

def optimal_graph_coloring( G, start_from = 2 ):
    num_colors = start_from
    solver = z3_solver()
    while not graph_coloring( G, num_colors, solver ):
        print "try with %d" % num_colors
        num_colors += 1

        if num_colors == G.number_of_nodes():
            exit( 1 )

        solver = z3_solver()

    return num_colors




# Main Program
G = nx.dodecahedral_graph()

optimal_graph_coloring( G )

nx.draw( G, node_color = [ p['color'] for _, p in G.nodes( data = True ) ] )
plt.draw()
plt.show()
