
from metasmt.core import *
from metasmt.support import bits_for_values

class rectangle(object):
  """a symbolic rectangle on a square field (limit x limit) """
  def __init__(self, limit):

    ## how many bits are requred for limit
    self.bitwidth =  bits_for_values( limit )


    ## store the upper bound (already as metasmt Expression)
    self.limit  = bv_uint(limit)[self.bitwidth]

    ## create the bounding box for the rectangle
    ## lower left corner, width, height
    self.xpos = new_bitvector(self.bitwidth)
    self.ypos = new_bitvector(self.bitwidth)
    self.xwid = new_bitvector(self.bitwidth)
    self.yhei = new_bitvector(self.bitwidth)

  def constraints(self):

    ##         vvvv bit-vector unsigned less equal
    x_in_lim = bv_ule(
                bv_add( zero_extend(1, self.xpos),
                        zero_extend(1, self.xwid)),
                zero_extend(1,self.limit)
    )
    y_in_lim = bv_ule( bv_add( self.ypos, self.yhei), self.limit )

    ##         vvvv bit-vector unsigned greater than
    wid_gt_0 = bv_ugt( self.xwid, bv_uint(0)[self.bitwidth] )
    hei_gt_0 = bv_ugt( self.yhei, bv_uint(0)[self.bitwidth] )

    ## all these comparisons operate on bitvector and return boolean symbols

    return logic_and(
        logic_and( x_in_lim, y_in_lim),
        logic_and( wid_gt_0, hei_gt_0)
      )

  def intersects(self):
    pass

  def print_solution(self, solver):
    print (
      solver.read_value(self.xpos),
      solver.read_value(self.ypos),
      solver.read_value(self.xwid),
      solver.read_value(self.yhei),
    )


def main():
  for name, sc in  available_solvers().items():
    try:
      rect = rectangle(5)
      print "testing solver", name
      solver = sc()
      solver.assertion( rect.constraints() )
      for i in xrange(5):
        if solver.solve():
          rect.print_solution(solver)
        else:
          print "no rect found"
    except:
      print "error in solver", name

if __name__ == '__main__':
   main()

