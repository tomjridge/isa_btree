#!/bin/bash

# execute various commands on a store

FN=/tmp/store
MAIN=main.native

rm -f /tmp/store
./$MAIN kv $FN init 
./$MAIN kv $FN insert k1 v1
./$MAIN kv $FN list

