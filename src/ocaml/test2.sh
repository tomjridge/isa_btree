#!/bin/bash

echo "[0,3,6,7,8,9]" | ./a.out test 


# echo "[0,1,2,3,4,5,6,7,8,9]" | ./a.out test 


time (echo "[0,2,3,4,7,8,9,10, 11,15,16,20]" | ./a.out test)
