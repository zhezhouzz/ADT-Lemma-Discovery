module Ast = Language.SpecAst
module Value = Pred.Value
module Axiom = Inference.AxiomSyn;;
module Spec = Inference.SpecSyn;;

open Ast
open Utils
open Z3
open Printf
module SE = E.SE
module T = Tp.Tp
module V = Pred.Value
open Language.Helper
open Bench_utils
;;
let testname = "batchedq" in
(* let tail =
 *   match r with
 *   | [], _ -> raise Empty
 *   | _ :: f, r ->
 *     if f = [] then List.rev r, f else f, r *)
let ctx = init () in
let spec_tab = StrMap.empty in
let spec_tab, _ = register spec_tab
    {name = "ListCons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.I h; V.L t] -> [V.L (h :: t)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, _ = register spec_tab
    {name = "ListIsEmpty"; intps = [T.IntList]; outtps = [T.Bool];
     prog = function
       | [V.L []] -> [V.B false]
       | [V.L _] -> [V.B true]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, _ = register spec_tab
    {name = "ListRev"; intps = [T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L l] -> [V.L (List.rev l)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let cons h t l = SpecApply ("ListCons", [h;t;l]) in
let tail l1 l2 l3 l4 = SpecApply ("Tail", [l1;l2;l3;l4]) in
let is_empty l = SpecApply ("ListIsEmpty", [l]) in
let rev l1 l2 = SpecApply ("ListRev", [l1;l2]) in
let f, r = map_double list_var ("f", "r") in
let vc =
  Implies (cons x f l1,
           And [
             Implies(And[is_empty f;rev r l2;], tail l1 r l2 f);
             Implies(Not (is_empty f), tail l1 r f r)
           ]
          )
in
let preds = ["list_once"; "list_member"; "list_order"; "list_head"; "list_last"; "list_next"] in
let bpreds = ["=="] in
let _ = print_vc_spec vc spec_tab in
let spec_tab = add_spec spec_tab "Tail" ["l1";"l2";"l3";"l4"] ["u"]
    (E.And [
        E.Iff (Or[list_member l3 u; list_head l1 u; list_member l4 u;],
               E.Or [list_member l1 u; list_member l2 u]);
      ])
in
let _ = printf_assertion spec_tab ["Tail"] in
let axiom1 = assertion ~startX:2 ~maxX:2 ctx vc spec_tab
    ["list_member"; "list_order"; "list_head"]
    bpreds 150 8 true testname "2" in
let axiom12 = assertion ~startX:2 ~maxX:2 ctx vc spec_tab
    ["list_last";"list_member"; "list_order"; "list_head"]
    bpreds 150 8 true testname "5" in
(* let axiom13 = assertion ~startX:3 ~maxX:3 ctx vc spec_tab
 *     ["list_member"; "list_order"; "list_head"]
 *     bpreds 150 8 true testname "3" in *)
(* let _ = axiom_eq ctx axiom1 axiom3 in *)
(* let _ = raise @@ InterExn "zz" in *)
(* let axiom14 = assertion ~startX:4 ~maxX:4 ctx vc spec_tab
 *     ["list_member"; "list_order"; "list_head"]
 *     bpreds 200 7 true testname "4" in
 * let axiom15 = assertion ~startX:5 ~maxX:5 ctx vc spec_tab
 *     ["list_member"; "list_order"; "list_head"]
 *     bpreds 200 7 true testname "5" in *)
let axiom16 = assertion ~startX:3 ~maxX:3 ctx vc spec_tab
    ["list_last"; "list_member"; "list_order"; "list_head";]
    bpreds 150 8 true testname "6" in
let axiom17 = assertion ~startX:3 ~maxX:3 ctx vc spec_tab
    ["list_last";"list_next";"list_member"; "list_order"; "list_head";]
    bpreds 150 8 true testname "7" in
let _ = to_verifier testname [axiom1;axiom12;
                              (* axiom13;axiom14;axiom15; *)
                              axiom16;axiom17]in
let _ = raise @@ InterExn "zz" in


let spec_tab = add_spec spec_tab "Tail" ["l1";"l2";"l3";"l4"] ["u";"v"]
    (E.And [
        E.Iff (Or[list_member l3 u; list_member l4 u; list_head l1 u],
               E.Or [list_member l1 u; list_member l2 u]);
        E.Implies (Or[list_order l3 u v; list_order l4 v u],
                   Or[list_order l1 u v; list_order l2 v u])
      ])
in
let _ = printf_assertion spec_tab ["Tail"] in
let axiom2 = assertion ctx vc spec_tab
    ["list_member"; "list_order"; "list_head"; "list_next"]
    bpreds 200 8 true testname "axiom2" in

(* let spec_tab = add_spec spec_tab "Tail" ["l1";"l2";"l3";"l4"] ["u"]
 *     (E.Iff (Or[list_member l3 u; list_member l4 u],
 *                E.Or [list_member l1 u; list_member l2 u]))
 * in
 * let axiom3 = assertion ctx vc spec_tab preds bpreds false testname "axiom3" in
 * 
 * let spec_tab = add_spec spec_tab "Tail" ["l1";"l2";"l3";"l4"] ["u"]
 *     (E.Implies (list_head l1 u, list_head l4 u))
 * in
 * let axiom4 = assertion ctx vc spec_tab preds bpreds false testname "axiom4" in *)
let _ = to_verifier testname [axiom1;axiom2] in
();;
