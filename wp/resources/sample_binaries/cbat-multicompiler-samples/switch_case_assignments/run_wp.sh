# This test compares our switch_case_assignment example that has been
# compiled with multiple compilers

# Should return UNSAT

set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap wp \
    --func=process_status \
    --compare-final-reg-values=RAX \
    -- switch_case_assignments-23908 switch_case_assignments-26471
}

compile && run
