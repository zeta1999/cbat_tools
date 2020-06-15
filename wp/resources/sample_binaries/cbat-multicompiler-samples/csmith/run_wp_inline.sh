# This test compares csmith.c compiled with different compilers.

# This test inlines all function calls rather than using function summaries.

# Should return UNSAT

set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --compare-final-reg-values=RAX \
    --use-constant-chaosing \
    --inline=.* \
    -- csmith-10684 csmith-16812
}

compile && run
