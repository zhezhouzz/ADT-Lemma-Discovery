#!/bin/bash
host_dir=".elrond"
name=$1
num=$2
if [ "$3" = "to-murphy" ]; then
	dune exec -- main/main.exe infer consistent data/$name.ml data/($name)_assertion$num.ml $name$num.elrond >.out
	cp $name$num.elrond/_beforeweakening.json $host_dir/$name$num.elrond_beforeweakening.json
fi

if [ "$3" = "weakening" ]; then
	dir $name$num.elrond
	cp $host_dir/$name$num.elrond_beforeweakening.json $name$num.elrond/_beforeweakening.json
	dune exec -- main/main.exe infer weakening $name$num.elrond > $name$num.elrond.out
fi

if [ "$3" = "weakening-murphy" ]; then
	dir $name$num.murphy
	cp $host_dir/$name$num.elrond_beforeweakening.json $name$num.murphy/_beforeweakening.json
	dune exec -- main/main.exe infer weakening-murphy data/$name.ml data/($name)_assertion$num.ml $host_dir/_$name$num.elrond.spectable $host_dir/_$name$num.elrond.alpha.murphy $name$num.murphy > $name$num.murphy.out
fi
