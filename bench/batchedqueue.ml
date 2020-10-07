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
(* let tail =
 *   match r with
 *   | [], _ -> raise Empty
 *   | _ :: f, r ->
 *     if f = [] then List.rev r, f else f, r *)
let ctx = init () in
let spec_tab = StrMap.empty in
let spec_tab, _ = register spec_tab
    {name = "Cons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.I h; V.L t] -> [V.L (h :: t)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, _ = register spec_tab
    {name = "IsEmpty"; intps = [T.IntList]; outtps = [T.Bool];
     prog = function
       | [V.L []] -> [V.B false]
       | [V.L _] -> [V.B true]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, _ = register spec_tab
    {name = "Rev"; intps = [T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L l] -> [V.L (List.rev l)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let cons h t l = SpecApply ("Cons", [h;t;l]) in
let tail l1 l2 l3 l4 = SpecApply ("Tail", [l1;l2;l3;l4]) in
let is_empty l = SpecApply ("IsEmpty", [l]) in
let rev l1 l2 = SpecApply ("Rev", [l1;l2]) in
let f, r = map_double list_var ("f", "r") in
let vc =
  Implies (cons x f l1,
           And [
             Implies(And[is_empty f;rev r l2;], tail l1 r l2 f);
             Implies(Not (is_empty f), tail l1 r f r)
           ]
          )
in
let spec_tab = add_spec spec_tab "Tail" ["l1";"l2";"l3";"l4"] ["u";"v"]
    (E.And [
        E.Iff (Or[list_member l3 u; list_member l4 u; list_head l1 u],
               E.Or [list_member l1 u; list_member l2 u]);
      ])
in
let axiom = assertion ctx vc spec_tab in
let _ = printf "axiom:\n\t%s\n" (E.pretty_layout_forallformula axiom) in

let spec_tab = add_spec spec_tab "Tail" ["l1";"l2";"l3";"l4"] ["u";"v"]
    (E.And [
        E.Iff (Or[list_member l3 u; list_member l4 u; list_head l1 u],
               E.Or [list_member l1 u; list_member l2 u]);
        E.Implies (Or[list_order l3 u v; list_order l4 v u],
                   Or[list_order l1 u v; list_order l2 v u])
      ])
in
let axiom = assertion ctx vc spec_tab in
let _ = printf "axiom:\n\t%s\n" (E.pretty_layout_forallformula axiom) in
();;