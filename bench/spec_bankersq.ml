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
let testname =  "bankersq" in
let ctx = init () in
let f, r, nu_lazy1, nu_reverse, nu_cons, lnil, nu_lazy2 =
  map7 list_var ("f","r","nu_lazy1", "nu_reverse", "nu_cons", "lnil", "nu_lazy2") in
let f1, r1 = map_double list_var ("f1", "r1") in
let x, lenf, lenr, lenf1, lenr1 =
  map5 int_var ("x", "lenf", "lenr", "lenf1", "lenr1") in
let nu_le = bool_var "nu_le" in
let preds = ["list_member"; "list_head"; "list_order"] in
let bpreds = ["=="] in
let is_empty, is_empty_hole = make_hole "is_empty" [T.Bool;T.IntList;] in
let cons, cons_hole = make_hole "cons" [T.Int; T.IntList; T.IntList] in
let reverse, reverse_hole = make_hole "reverse" [T.IntList; T.IntList] in
let concat, concat_hole = make_hole "concat" [T.IntList; T.IntList; T.IntList] in
let liblazy, liblazy_hole = make_hole "liblazy" [T.IntList; T.IntList] in
let trace1_value = [
  "is_empty", [V.B false;V.L [2;3];];
  "cons", [V.I 2; V.L [3]; V.L [2;3];];
  "cons", [V.I 2; V.L [1]; V.L [2;1];];
  "liblazy", [V.L [2;1];V.L [2;1];];
  "liblazy", [V.L [];V.L [];];
  "reverse", [V.L [3;2;1];V.L [1;2;3];];
  "reverse", [V.L [];V.L [];];
  "concat", [V.L [3;2;1];V.L [1]; V.L [3;2;1;1];];
] in
let trace2_value = [
  "is_empty", [ V.B true; V.L [];];] in
let spectable = predefined_spec_tab in
let snoc args = SpecApply ("Snoc", args) in
let vc =
  Implies(And[
      intadd [lenr;const1;lenr1];
      cons [x; r; nu_cons;];
      liblazy [nu_cons; r1];
    ],
          Ast.Ite(le [nu_le; lenr1; lenf],
                  snoc [lenf;f;lenr;r;x;lenf;f;lenr1;r1],
                  Implies(
                    And [intadd [lenf;lenr1;lenf1];
                         reverse [r1;nu_reverse];
                         concat [f;nu_reverse;f1];
                         is_empty [booltrue; lnil];
                         liblazy [lnil; nu_lazy2];
                        ],
                    snoc [lenf;f;lenr;r;x;lenf1;f1;const0;nu_lazy2]
                  )
                 )
    )
in
let vcs = Ast.eliminate_cond vc in
let holes = [is_empty_hole; cons_hole; liblazy_hole; concat_hole; reverse_hole;] in
let traces = [trace1_value; trace2_value] in
let f, f', r, r' = map4 list_var ("f", "f'", "r", "r'") in
let spectable = add_spec spectable "Snoc"
    ["lenf";"f";"lenr";"r";"x";"lenf'";"f'";"lenr'";"r'"] ["u"]
    (Iff(Or[list_member f u; list_member r u; int_eq u x],
         Or[list_member f' u; list_member r' u]
        ))
in
let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
(* let spectable = add_spec spectable "Snoc"
 *     ["lenf";"f";"lenr";"r";"x";"lenf'";"f'";"lenr'";"r'"] ["u"]
 *     (Iff(Or[list_member f u; list_member r u],
 *          Or[And[list_member f' u; list_member r' x]; list_order r' x u; list_order f' u x]
 *         ))
 * in
 * let _ = test ctx vcs spectable holes preds bpreds 2 2 traces in *)
();;
