compile() {
        make
}

run() {
        bap wp --func=main --loop-unroll=2 -- main
}

clean() {
        make clean
}

clean && compile && run
