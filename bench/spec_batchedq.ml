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
let testname = "batchedq" in
let ctx = init () in
let l1, f, r, nu_rev=
  map4 list_var ("l1", "f","r", "nu_rev") in
let nu_empty = bool_var "nu_empty" in
let preds = ["list_member"; "list_head"; "list_order"] in
let bpreds = ["=="] in
let is_empty, is_empty_hole = make_hole "is_empty" [T.Bool;T.IntList;] in
let cons, cons_hole = make_hole "cons" [T.Int; T.IntList; T.IntList] in
let rev, rev_hole = make_hole "rev" [T.IntList; T.IntList] in
let trace1_value = [
  "is_empty", [V.B false;V.L [2;3];];
  "cons", [V.I 2; V.L [3]; V.L [2;3];];
  "cons", [V.I 2; V.L [1]; V.L [2;1];];
] in
let trace2_value = [
  "is_empty", [ V.B true; V.L [];];] in
let spectable = predefined_spec_tab in
let tail args = SpecApply ("Tail", args) in
let vc =
  Implies(cons [x;f;l1],
          Ite(is_empty [nu_empty;f],
              Implies(rev [r;nu_rev], tail [l1;r;nu_rev;f]),
              tail [l1;r;f;r]
             )
         )
    in
let vcs = Ast.eliminate_cond vc in
let holes = [is_empty_hole; cons_hole; rev_hole] in
let traces = [trace1_value; trace2_value] in
let spectable = add_spec spectable "Tail" ["l1";"l2";"l3";"l4"] ["u"]
    (E.And [
        E.Iff (Or[list_member l3 u; list_head l1 u; list_member l4 u;],
               E.Or [list_member l1 u; list_member l2 u]);
      ])
in
let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
let spectable = add_spec spectable "Tail" ["l1";"l2";"l3";"l4"] ["u";"v"]
    (E.And [
        E.Iff (Or[list_member l3 u; list_member l4 u; list_head l1 u],
               E.Or [list_member l1 u; list_member l2 u]);
        E.Implies (Or[list_order l3 u v; list_order l4 v u],
                   Or[list_order l1 u v; list_order l2 v u])
      ])
in
let _ = test ctx vcs spectable holes preds bpreds 2 2 traces in
();;
