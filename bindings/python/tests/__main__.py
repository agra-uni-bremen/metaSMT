import os
import re
import sys
import random
import unittest

test_str_re = re.compile(r'([^ ]+) \((.*)\)')

def test_id(test):
  m = test_str_re.match(str(test))
  if m is None:
    return None

  t, h = m.groups()

  return tuple(h.split('.')+[t])

def map_tests(fun, test):
  if isinstance(test, unittest.suite.TestSuite):
    map(lambda t: map_tests(fun, t), test)
  else:
    fun(test)

def print_test(test):
    print '.'.join(test_id(str(test)))

def collect_tests(dic):
  def fun(test):
    id = test_id(test)
    dic[id] = test
  return fun


if __name__ == "__main__":
    tests = unittest.defaultTestLoader.discover(os.path.dirname(__file__), pattern='*.py')
    if len(sys.argv) == 2 and sys.argv[1] == '--discover':
      map_tests(print_test, tests)
    else:
      random.seed()
      if len(sys.argv) == 0:
        unittest.main()
      else:
        lookup = {}
        map_tests( collect_tests(lookup), tests)
        suite = unittest.TestSuite()
        for t in sys.argv[1:]:
           tc = lookup[tuple(t.split('.'))]
           suite.addTest(tc)
        unittest.TextTestRunner(verbosity=2).run(suite)
