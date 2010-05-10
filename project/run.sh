#!/bin/bash

cd classes/

bits=$3

if test -z $bits; then
	bits=64
fi

java zinara.$1 $2 $bits
