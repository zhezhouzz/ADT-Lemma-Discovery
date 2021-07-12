#!/bin/bash

export LD_LIBRARY_PATH=`opam var z3:lib`:"$LD_LIBRARY_PATH"
export DYLD_LIBRARY_PATH=`opam var z3:lib`:$DYLD_LIBRARY_PATH

config=config/prebuilt.config
python3 evaluation_tool.py table $config
python3 evaluation_tool.py figure $config
