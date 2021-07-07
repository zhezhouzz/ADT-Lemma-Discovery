#!/bin/bash

export LD_LIBRARY_PATH=`opam var z3:lib`:"$LD_LIBRARY_PATH"
export DYLD_LIBRARY_PATH=`opam var z3:lib`:$DYLD_LIBRARY_PATH

action=$1

for name in "customstk"
do
    for i in {1..3}
    do
        dune exec -- main/main.exe infer $action data/$name.ml data/"$name"_assertion$i.ml benchmark_$name$i > log.txt
        mv log.txt _benchmark_$name$i/log.txt
    done
done

motivation=motivation
motivationfile=customstk
dune exec -- main/main.exe infer $action data/"$motivationfile".ml data/"$motivationfile"_assertion1.ml benchmark_$motivation -sb 4 > log.txt
mv log.txt _benchmark_$motivation/log.txt
