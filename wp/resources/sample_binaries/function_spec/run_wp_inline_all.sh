# This test contains a call to foo which returns 3. In main, in the case that
# foo returns 5, we assert_fail. This should be impossible.

# This tests that WP can inline all functions. With foo inlined, we can determine
# that it only returns 3, and we know that the assert_fail cannot be reached.

# Should return UNSAT.

set -x

compile () {
  make
}

run () {
    bap main --pass=wp --wp-inline=.* --wp-trip-asserts
}

compile && run
