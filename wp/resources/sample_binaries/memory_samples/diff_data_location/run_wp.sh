# Tests having different locations for the data section and same values on the
# stack. The binaries are the same except for the location of val in the data
# section.

# Because val's address is different between the binaries, Z3 can create a
# countermodel where the data at the modified binary's address differs from the
# data at the original binary's address.

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
    -- main_1 main_2
}

compile && run
