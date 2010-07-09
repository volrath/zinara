#!/bin/bash

for i in `seq $1`;
do
    echo -ne '\nEJEMPLO ' $i ' -----------------------------------------------------\n';
    cat misc`echo $i`.zn;
    echo -ne '\n'
done
