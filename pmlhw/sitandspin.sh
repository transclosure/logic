#!/bin/sh
spin -a $1
gcc -o pan pan.c
echo "VERIFY NO CYCLES---------------------------------------------"
./pan -n
echo "VERIFY WITH CYCLES-------------------------------------------"
./pan -n -a
#spin -t -p $1
rm -f $1.trail
