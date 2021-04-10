#!/bin/bash

export LD_LIBRARY_PATH="/Users/zhezhou/.opam/4.06.0/lib/:$LD_LIBRARY_PATH"
export DYLD_LIBRARY_PATH=`opam var z3:lib`:$DYLD_LIBRARY_PATH

echo "" > log_diff.text
name="trie"
for i in {1..1}
do
    dune exec bench/spec_$name.exe $i diff >> log_diff.text
done
for name in "bankersq" "batchedq" "leftisthp" "rbset" "uniquel"
do
  for i in {1..2}
  do
      dune exec bench/spec_$name.exe $i diff >> log_diff.text
  done
done
for name in "splayhp" "stream"
do
    for i in {1..3}
    do
        dune exec bench/spec_$name.exe $i diff >> log_diff.text
    done
done
for name in "customstk" "unbset"
do
    for i in {1..4}
    do
        dune exec bench/spec_$name.exe $i diff >> log_diff.text
    done
done
