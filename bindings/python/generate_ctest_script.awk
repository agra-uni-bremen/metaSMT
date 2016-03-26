#!/usr/bin/awk
BEGIN {
}

{
  test=$1
  gen_test(test)
}

function gen_test(name) {
  print "ADD_TEST(\"" name "\"\n cmake -E chdir " path " \"" pymetaSMT "\" \"tests\" \"" name "\")"
  print "set_tests_properties(\"" name "\"\n PROPERTIES TIMEOUT " testtime ")"
}
