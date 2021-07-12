#!/bin/bash

export LD_LIBRARY_PATH=`opam var z3:lib`:"$LD_LIBRARY_PATH"
export DYLD_LIBRARY_PATH=`opam var z3:lib`:$DYLD_LIBRARY_PATH

config=config/result_table4.config
python3 build_table4.py diff $config
python3 build_table4.py count $config
python3 build_table4.py table $config
