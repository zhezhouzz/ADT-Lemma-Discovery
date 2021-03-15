module Ast = Language.SpecAst
module Value = Pred.Value
module SpecAbd = Inference.SpecAbduction;;

open Ast
open Utils
open Z3
open Printf
module SE = E.SE
module T = Tp.Tp
module V = Pred.Value
open Language.Helper
open Bench_utils
open Frontend.Fast.Fast
;;
let testname = "uniquel" in
let ctx = init () in
let x, x1, nu_set_add, nu =
  map4 list_var ("x","x1","nu_set_add", "nu") in
let a, a1 =
  map_double int_var ("a", "a1") in
let nu_eq, nu_empty = map_double bool_var ("nu_eq", "nu_empty") in
let preds = ["list_member"; "list_head"; "list_once"] in
let bpreds = ["=="] in
let is_empty, is_empty_hole = make_hole "is_empty" [T.Bool;T.IntList;] in
let cons, cons_hole = make_hole "cons" [T.Int; T.IntList; T.IntList] in
let trace1_value = [
  "is_empty", [V.B false;V.L [2;3];];
  "cons", [V.I 2; V.L [3]; V.L [2;3];];
  "cons", [V.I 2; V.L [1]; V.L [2;1];];
] in
let trace2_value = [
  "is_empty", [ V.B true; V.L [];];] in
let spectable = predefined_spec_tab in
let set_add args = SpecApply ("SetAdd", args) in
let vc =
  Ast.Ite (is_empty [nu_empty; x],
           Implies (cons [a;x;nu],
                    set_add [a;x;nu]
                   ),
           Implies (cons [a1;x1;x],
                    Ite(inteq [nu_eq;a;a1;],
                        Implies(cons [a1;x1;nu], set_add [a;x;nu]),
                        Implies(And[
                            set_add [a;x1;nu_set_add];
                            cons [a1;nu_set_add;nu]
                          ], set_add [a;x;nu])
                       )
                   )
          )
in
let vcs = Ast.eliminate_cond vc in
let holes = [is_empty_hole; cons_hole;] in
let traces = [trace1_value; trace2_value] in
let spectable = add_spec spectable "SetAdd" ["x";"l1";"l2"] ["u";]
    (E.And [
        E.Iff(list_member l2 u, E.Or [int_eq u x; list_member l1 u]);
      ])
in
let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
let spectable = add_spec spectable "SetAdd" ["x";"l1";"l2"] ["u";]
    (E.And [
        E.Implies (list_once l1 u, list_once l2 u);
        E.Iff(list_member l2 u, E.Or [int_eq u x; list_member l1 u]);
      ])
in
let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
();;
