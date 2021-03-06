# A simple test that shows an instance where WP catches a function that has
# different return values between the two binaries. In this case, main_1 returns
# a 2 and main_2 returns a 5.

# Should return SAT

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
    --wp-file2=main_2.bpj
}

compile && run
