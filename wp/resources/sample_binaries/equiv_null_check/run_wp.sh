# The modified binary adds a null check after the call to malloc. In the case
# that malloc returns NULL, the modified binary will hit an assert_fail.

# Should return SAT.

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --compare-final-reg-values=RAX \
    -- main_1 main_2
}

compile && run
