#!/bin/bash

export LD_LIBRARY_PATH=`opam var z3:lib`:"$LD_LIBRARY_PATH"
export DYLD_LIBRARY_PATH=`opam var z3:lib`:$DYLD_LIBRARY_PATH

config=config/standard.config
tool=bin/evaluation_tool.py
python3 $tool consistent $config
python3 $tool weakening $config -l

python3 $tool diff $config
python3 $tool count $config -l
