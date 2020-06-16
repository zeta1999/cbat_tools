# This test compares csmith.c compiled with different compilers.

# This test inlines all function calls rather than using function summaries.

# Should return UNSAT

set -x

run () {
  bap wp \
    --func=main \
    --compare-final-reg-values=RAX \
    --use-constant-chaosing \
    --inline=.* \
    --no-byteweight \
    -- csmith-10684 csmith-16812
}

run
