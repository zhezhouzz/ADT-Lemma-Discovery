#!/bin/bash

export LD_LIBRARY_PATH=`opam var z3:lib`:"$LD_LIBRARY_PATH"
export DYLD_LIBRARY_PATH=`opam var z3:lib`:$DYLD_LIBRARY_PATH

dune build
rm -f main.exe
cp _build/default/main/main.exe main.exe