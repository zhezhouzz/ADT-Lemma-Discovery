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
let testname = "stream" in
let ctx = init () in
let argl1 = T.IntList, "l1" in
let argl2 = T.IntList, "l2" in
let argnu_l = T.IntList, "nu_l" in
let preds = ["list_member"; "list_head"; "list_order"] in
let bpreds = ["=="] in
let trace1_value = [
  "is_empty", [V.B false;V.L [2;3];];
  "cons", [V.I 2; V.L [3]; V.L [2;3];];
  "cons", [V.I 2; V.L [1]; V.L [2;1];];
  "liblazy", [V.L [2;1];V.L [2;1];];
  "libforce", [V.L [3;2;1];V.L [3;2;1];];
  "liblazy", [V.L [];V.L [];];
  "libforce", [V.L [];V.L [];];
] in
let trace2_value = [
  "is_empty", [ V.B true; V.L [];];] in
let is_empty, is_empty_hole = make_hole "is_empty" [T.Bool;T.IntList;] in
let cons, cons_hole = make_hole "cons" [T.Int; T.IntList; T.IntList] in
let liblazy, liblazy_hole = make_hole "liblazy" [T.IntList; T.IntList] in
let libforce, libforce_hole = make_hole "libforce" [T.IntList; T.IntList] in
let spectable = predefined_spec_tab in
let s, acc, tl, nu_cons, nu_lazy, nu_reverse, nu =
  map7 list_var ("s", "acc", "tl", "nu_cons", "nu_lazy", "nu_reverse", "nu") in
let nu_is_empty = bool_var "nu_is_empty" in
let hd = int_var "hd" in
let reverse args = SpecApply ("Reverse", args) in
let vc =
  Ast.Ite (is_empty [nu_is_empty; s;],
           Implies (liblazy [acc; nu_lazy],
                    reverse [acc; s; nu_lazy]
                   ),
           Implies (And [cons [hd; tl; s];
                         cons [hd; acc; nu_cons];
                         liblazy [nu_cons; nu_lazy];
                         reverse [nu_lazy; tl; nu_reverse];
                         libforce [nu_reverse; nu]],
                    reverse [acc; s; nu])
          )
in
let vcs = Ast.eliminate_cond vc in
let holes = [is_empty_hole; cons_hole; liblazy_hole; libforce_hole;] in
let traces = [trace1_value; trace2_value] in
let spectable = add_spec spectable "Reverse" ["l1";"l2";"l3"] ["u"]
    (E.And [
        E.Implies (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
      ])
in
let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
let spectable = add_spec spectable "Reverse" ["l1";"l2";"l3"] ["u";"v"]
    (E.And [
        E.Implies (E.Or [list_order l1 u v;
                         list_order l2 v u;
                         E.And [list_member l2 u; list_member l1 v]],
                   list_order l3 u v);
        E.Iff (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
      ])
in
let _ = test ctx vcs spectable holes preds bpreds 2 2 traces in
();;
