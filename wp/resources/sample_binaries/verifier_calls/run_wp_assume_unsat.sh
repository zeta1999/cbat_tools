# This tests the function spec to __VERIFIER_assume. If the assumption that
# x > 0 holds, it is impossible to hit the case where there is a __VERIFIER_error.

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap verifier_assume_unsat --pass=wp --wp-trip-asserts
}

compile && run
