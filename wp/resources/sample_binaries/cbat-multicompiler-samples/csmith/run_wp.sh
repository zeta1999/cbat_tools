# This test compares csmith.c compiled with different compilers

# Should return UNSAT

set -x

run () {
  bap wp \
    --func=main \
    --compare-final-reg-values=RAX \
    --use-constant-chaosing \
    --no-byteweight \
    -- csmith-10684 csmith-16812
}

run
