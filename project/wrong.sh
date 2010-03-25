#!/bin/bash

for i in `ls -1 $1/w_*`
do
    if ./run.sh Main $1/$i &> /dev/null
    then
	echo "Error para la instancia $i, deberia fallar"
    else
	echo "Fallo la instancia $i"
    fi
done
