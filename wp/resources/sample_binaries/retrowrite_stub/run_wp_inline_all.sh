# Stubs the lines of assembly that retrowrite adds to the beginning of each
# label. At the end of the subroutine, the registers between both binaries
# should be equal.

# This inlines all function calls which should pop
# the stack pointer at the end of each call.

# Should return UNSAT

set -x

dummy_dir=../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-compare-post-reg-values=RAX \
    --wp-file1=main_1.bpj \
    --wp-file2=main_2.bpj \
    --wp-inline=.*
}

compile && run
