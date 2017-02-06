#!/bin/bash

bin=./test_in_mem.native

echo "[0,3,6,7,8,9]" | $bin test 


# echo "[0,1,2,3,4,5,6,7,8,9]" | ./a.out test 


time (echo "[0,2,3,4,7,8,9,10, 11,15,16,20]" | $bin test)


# #
# 
# 2016-12-02
# 
# $ ocaml $ ./test2.sh 
# test: reading input from stdin
# test: read [0,3,6,7,8,9]
# test: starting while
# ...........Tests passed; num states explored: 101
# test: reading input from stdin
# test: read [0,2,3,4,7,8,9,10,11,15,16,20]
# test: starting while
# .........................Tests passed; num states explored: 44102
# 
# real	0m36.724s
# user	0m35.008s
# sys	0m1.744s
# 
# 
# 
# 
