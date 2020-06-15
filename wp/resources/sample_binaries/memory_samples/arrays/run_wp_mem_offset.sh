# A test where the function foo_get indexes the array foo with length 10. The
# address of foo is different between the two binaries.

# This test turns on the mem_offset flag, which equates the memory values of the
# original binary with that of the modified binary at an offset. However, since
# foo has a length of 10, if the input to foo_get is greater than or equal to 10,
# we are indexing outside of the array, getting undefined behavior.

# Should return SAT

set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap wp \
    --func=foo_get \
    --compare-final-reg-values=RAX,RBX,RSP,RBP,R12,R13,R14,R15 \
    --mem-offset \
    -- main_1 main_2
}

compile && run
