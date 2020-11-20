# ADT-Lemma-Discovery
Algebraic data type lemma discovery

## Structure

- utils
- tp
  + types
- ml
  + decistion tree implementation(external library)
- pred
  + implemetation of the ADT predicates(member, order...)
- solver
  + SMT solver wrapper
- language
  + the specification language, which if limited first-order logic with ADT predicates
- inference
  + spec/lemma inference
- test
- bench
  + benchmarks

## Dependency

- ocaml version: ocaml-base-compiler.4.08.1
- z3 version: z3.4.7.1
- dafny(optional): version 2.3.0

## Test

+ run 

```
export DUNE_ROOT=`pwd`
```

To setup the environment.

+ run `dune exec bench/$benchname.exe` to run infer the lemmas. E.g. `dune exec bench/customstack.exe` which includes all benchmarks in Custom Stack.

+ (optional) If you want to verify the inferred lemma, run `dafny lemma_verifier/$benchname.dfy`. E.g. `dafny lemma_verifier/custstk.dfy`.
