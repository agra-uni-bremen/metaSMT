BEGIN {
  PREFIX=""
}

$0 ~ "^ *BOOST_FIXTURE_TEST_SUITE.*\\(" {
  sub("^.*\\( *", "");
  sub(" *\\,.*$", "");
  PREFIX=$0;
}

$0 ~ "^ *BOOST_AUTO_TEST_SUITE_END *\\( *\\)" {
  PREFIX=""
}

$0 ~ "^ *BOOST_AUTO_TEST_CASE *\\(" { 
  sub("^ *BOOST_AUTO_TEST_CASE *\\( *", "")
  sub(" *\\).*$", "")
  if ( PREFIX ) {
    printf "%s/%s\n", PREFIX, $0
  } else {
    printf "%s\n", $0
  }
}

$0 ~ "^ *#include  *\"" {
  sub("^[^\"]*\" *", "");
  sub(" *\".*$", "");
  #print "#include", $0
  callfile($0)
}

END {
}

function callfile(f) {
	if (system("test -f " f) == 0) {
		ARGV[ARGC]=f
		ARGC++
	}
}

# vim: ts=2 sw=2 et
