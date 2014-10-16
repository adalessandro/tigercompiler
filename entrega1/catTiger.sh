#!/bin/bash

FILE=$1;

if [ $FILE = "ALL" ]; then

for f in `ls ../tests/type/`; do ./catTiger.sh "../tests/type/$f"; done

else

(cat $FILE;
echo -e "----------------------------------------------\n";
./tiger -arbol -escapes $FILE) | less

fi
