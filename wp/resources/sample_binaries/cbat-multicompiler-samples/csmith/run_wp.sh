# This test compares csmith.c compiled with different compilers

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
    -- csmith-10684 csmith-16812
}

compile && run
