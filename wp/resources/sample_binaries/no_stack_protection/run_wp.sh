# This test compiles the same C file with and without stack protection.

# Should return SAT

set -x

dummy_dir=../dummy

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --compare-final-reg-values=RSI,RAX \
    -- main_1 main_2
}

compile && run
