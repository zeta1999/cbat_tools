# This tests that removing a switch case can result in a fall through to
# another case that is not intended.

# After removing the case to LOG_STATUS, the NAV case will fall through to
# DEPLOY, setting the deploy flag to true. In the original binary, deploy
# should be set to false at the end of execution.

# Should return SAT

set -x

dummy_dir=../dummy

compile () {
  make
}

run () {
  bap wp \
    --func=process_status \
    --compare-final-reg-values=RAX \
    -- main_1 main_2
}

compile && run
