#!/bin/sh
spin -a $1
gcc -o pan pan.c
./pan
./pan -a
# spin -t -p $1
