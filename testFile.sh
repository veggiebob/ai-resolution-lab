#!/bin/bash

testPath="./testcases"
PROG="./Main"

FILES="$testPath/*/*.cnf"
for fP in $FILES; do
		basename $fP
		#echo $PROG $fP
		#timeout -s 9 60s $PROG $fP
		$PROG $fP
done

#echo 

