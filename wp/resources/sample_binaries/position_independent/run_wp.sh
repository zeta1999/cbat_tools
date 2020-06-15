# This tests inlining a function that has been compiled with fPIC.
# init() returns different values, and if inlined properly, WP should be able
# to capture this.

# Should return SAT.

set -x

dummy_dir=../dummy

compile () {
  make FLAGS="-fPIC -shared"
}

run () {
  bap wp \
    --func=example \
    --compare-final-reg-values=RAX \
    --inline=init \
    -- main_1.so main_2.so
}

compile && run
