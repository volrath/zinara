#!/bin/bash

for i in `ls -1 classes/zinara/tests`
do
echo ------------${i//.class/}-----------
./test.sh ${i//.class/}
done

echo ------------Bad tests-------------
./wrong.sh test_files/grammar_and_ast/struct_insts
