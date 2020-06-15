# Tests having a different value in the data section (at the same addresses)
# and the same values on the stack.

# The test accumulates that values in the data section and stack and stores
# the result in RAX. Because the data section has different values, the output
# RAX also differs.

# Should return SAT

set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap wp \
    --func=__libc_start_main \
    --compare-final-reg-values=RAX \
    --no-byteweight \
    -- main_1 main_2
}

compile && run
