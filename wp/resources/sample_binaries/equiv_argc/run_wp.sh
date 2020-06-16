# The modified version of this test adds a check to argc and returns a
# different value if true. WP is able to determine that this is the case when
# argc is 2. (RDI = 2)

# Should return SAT

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
