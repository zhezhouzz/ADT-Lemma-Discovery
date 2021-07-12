#!/bin/bash

export LD_LIBRARY_PATH=`opam var z3:lib`:"$LD_LIBRARY_PATH"
export DYLD_LIBRARY_PATH=`opam var z3:lib`:$DYLD_LIBRARY_PATH

config=config/standard.config
python3 evaluation_tool.py consistent $config
python3 evaluation_tool.py weakening $config -s

python3 evaluation_tool.py diff $config
python3 evaluation_tool.py count $config -s
