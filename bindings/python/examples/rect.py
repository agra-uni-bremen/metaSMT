from metasmt.core import *
from metasmt.operators import *

class rectangle(object):
  def __init__(self, limit, bw):
    self.bw =  bw
    self.limit  = bv_uint(limit)[bw]
    self.xpos = new_bitvector(bw)
    self.ypos = new_bitvector(bw)
    self.xwid = new_bitvector(bw)
    self.yhei = new_bitvector(bw)

  def to_logic_expression(self):
    lim = self.limit
    return reduce(logic_and, (
      self.xpos + self.xwid <= lim,
      self.ypos + self.yhei <= lim,
      self.xwid > bv_uint(0)[self.bw],
      self.yhei > bv_uint(0)[self.bw],
      ))

  def print_solution(self, solver):
    print (
      solver[self.xpos],
      solver[self.ypos],
      solver[self.xwid],
      solver[self.yhei],
    )


def main():
  for name, sc in  available_solvers().items():
    try:
      rect = rectangle(5,4)
      print "testing solver", name
      solver = sc()
      solver &= rect.to_logic_expression()
      for i in xrange(5):
        if solver.solve():
          rect.print_solution(solver)
        else:
          print "no rect found"

    except Exception as e:
      print "error in solver", name
      print e

if __name__ == '__main__':
   main()

