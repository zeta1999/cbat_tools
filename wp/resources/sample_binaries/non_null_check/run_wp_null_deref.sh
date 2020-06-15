# This compares a binary that contains a memory read at RDI with another binary
# that contains a memory read at RDI + 1.

# This test turns on the check-null-deref flag. With this flag, we assume that
# if each memory read in the original binary reads a non-null address, then
# that same memory read will also be non-null in the modified binary. In this
# case, since we are reading at an offset of 1 from the original, we cannot assume
# that address is non-null.

# Should return SAT

set -x

dummy_dir=../dummy

compile () {
  make
}

run () {
  bap wp \
    --func=__libc_start_main \
    --compare-final-reg-values=RAX \
    --find-null-derefs \
    -- main_1 main_2
}

compile && run
