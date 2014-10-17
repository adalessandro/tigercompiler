#!/bin/bash

FILE=$1;

if [ $FILE = "ALL" ]; then

for f in `ls ../tests/good/`; do ./catTiger.sh "../tests/good/$f"; done

else

(cat $FILE;
echo -e "----------------------------------------------\n";
./tiger -arbol -escapes $FILE) | less

fi
