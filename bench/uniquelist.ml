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
open Frontend.Fast.Fast
;;
let testname = "uniquel" in
(* let rec set_add a x =
 *   match x with
 *   | [] -> [a]
 *   | a1 :: x1 =>
 *     if a == a1 then a1 :: x1 else a1 :: (set_add a x1) *)
let ctx = init () in
let spec_tab = predefined_spec_tab in
let _eq a b = SpecApply ("Eq", [a;b]) in
let spec_tab = add_spec spec_tab "Eq" ["a";"b"] [] (int_eq a b) in
let spec_tab, cons = register spec_tab
    {name = "Cons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
            prog = function
              | [V.I h; V.L t] -> [V.L (h :: t)]
              | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, is_empty = register spec_tab
    {name = "IsEmpty"; intps = [T.IntList]; outtps = [T.Bool];
     prog = function
       | [V.L []] -> [V.B false]
       | [V.L _] -> [V.B true]
       | _ -> raise @@ InterExn "bad prog"
    } in
(* let spec_tab = add_spec spec_tab "UListTail" ["l1";"l2"] [] (int_eq l1 l1) in *)
let set_add l = SpecApply ("SetAdd", l) in
let vc =
  Ast.Ite (is_empty [l1],
           Implies(cons [x; l1; l2], set_add [x; l1; l2]),
           Implies (cons [y; l3; l1],
                         Ite (_eq x y,
                              set_add [x; l1; l1],
                              Implies (And[set_add [x; l3; l4]; cons [y;l4;l5]],
                                       set_add [x; l1; l5])
                             )
                   )
      )
in
let preds = ["list_once"; "list_member"; "list_order"; "list_head"; "list_last"; "list_next"] in
let bpreds = ["=="] in
let _ = print_vc_spec vc spec_tab in
let spec_tab = add_spec spec_tab "SetAdd" ["x";"l1";"l2"] ["u";]
    (E.And [
        E.Iff(list_member l2 u, E.Or [int_eq u x; list_member l1 u]);
      ])
in
let _ = printf_assertion spec_tab ["SetAdd"] in
let axiom1 = assertion ctx vc spec_tab
    ["list_member"; "list_order"; "list_head";]
    bpreds 50 6 true testname "axiom1" in

let spec_tab = add_spec spec_tab "SetAdd" ["x";"l1";"l2"] ["u";]
    (E.And [
        E.Implies (list_once l1 u, list_once l2 u);
        E.Iff(list_member l2 u, E.Or [int_eq u x; list_member l1 u]);
      ])
in
let _ = printf_assertion spec_tab ["SetAdd"] in
let axiom2 = assertion ctx vc spec_tab
    ["list_member"; "list_order"; "list_head";"list_once"]
    bpreds 90 6 true testname "axiom2" in

let _ = to_verifier testname [axiom1;axiom2] in
();;
