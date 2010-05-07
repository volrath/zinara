#!/bin/bash
#set -o verbose
#set -o xtrace

bits=$2
file=$1

if test $bits != "64" -a $bits != "32" -a $bits != ""; then
	echo Arquitectura no soportada
	exit 1
fi

nasm -g -f elf${bits} $1 && \
ld -o ${file%".asm"} ${file%".asm"}.o
