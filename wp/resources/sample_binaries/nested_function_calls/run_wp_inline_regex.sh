# This test contains a function with two nested calls to foo then bar.

# This tests that we can inline both foo and bar with the regex passed into the
# inline flag, allowing WP to find the case where assert_fail is hit in bar.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap main --pass=wp --wp-inline="foo|bar" --wp-trip-asserts
}

compile && run
