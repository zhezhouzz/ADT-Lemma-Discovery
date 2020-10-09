# ADT-Spec-Inference
Algebraic data type specification inference

## Structure

- utils
- ml
  + decistion tree implementation(external library)
- pred
  + implemetation of the ADT predicates(order, order...)
- language
  + the specification language, which if limited first-order logic with ADT predicates
- axiom
  + axiom inference
- test

## Specification Evalution

As the specification(in EPR representation) is quantified by forall quantifier, the evaluation over epr tests finite assignments.

- Assume l := [1;2], eval(forall u v, order(l, u, v)) will be treated as:
 
 And (order([1;2], u, v)) where u v = 1, 2 or 3(3 can be any element which is not contained in the datatype instance), or:
 
```
order([1;2], 1, 1) && order([1;2], 1, 2) && order([1;2], 1, 3) &&
order([1;2], 2, 1) && order([1;2], 2, 2) && order([1;2], 2, 3) &&
order([1;2], 3, 1) && order([1;2], 3, 2) && order([1;2], 3, 3)
```

## Dependency

- ocaml version: ocaml-base-compiler.4.08.1
- z3 version: z3.4.7.1 (It seems has a bug in z3 4.8.x: https://github.com/Z3Prover/z3/issues/2305)

## Test

run 

```
DUNE_ROOT=`pwd` dune test
```

.
