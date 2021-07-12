#!/bin/bash

export LD_LIBRARY_PATH=`opam var z3:lib`:"$LD_LIBRARY_PATH"
export DYLD_LIBRARY_PATH=`opam var z3:lib`:$DYLD_LIBRARY_PATH

config=config/standard.config
tool=bin/evaluation_tool.py
python3 $tool table $config
python3 $tool figure $config
