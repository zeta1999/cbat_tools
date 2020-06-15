# This test compares equiv_argc that has been compiled with different compilers.

# Should return UNSAT

set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --compare-final-reg-value=RAX \
    -- equiv_argc-6404 equiv_argc-6487
}

compile && run
