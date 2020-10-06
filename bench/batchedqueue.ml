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
;;
(* let tail =
 *   match r with
 *   | [], _ -> raise Empty
 *   | _ :: f, r ->
 *     if f = [] then List.rev r, f else f, r *)
open Language.Helper;;
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
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Tail" ["l1";"l2";"l3";"l4"] ["u";"v"]
(E.And [
    E.Iff (Or[list_member l3 u; list_member l4 u; list_head l1 u], E.Or [list_member l1 u; list_member l2 u]);
  ])
in
let libcons = {name = "Cons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
            prog = function
              | [V.I h; V.L t] -> [V.L (h :: t)]
              | _ -> raise @@ InterExn "bad prog"
           } in
let libnil = {name = "IsEmpty"; intps = [T.IntList]; outtps = [T.Bool];
                prog = function
                  | [V.L []] -> [V.B false]
                  | [V.L _] -> [V.B true]
                  | _ -> raise @@ InterExn "bad prog"
               } in
let libreverse = {name = "Rev"; intps = [T.IntList]; outtps = [T.IntList];
                  prog = function
                    | [V.L l] -> [V.L (List.rev l)]
                    | _ -> raise @@ InterExn "bad prog"
                 } in
let spec_tab_add spec_tab {name;intps;outtps;prog} =
  StrMap.add name (Spec.infer ~progtp:(intps,outtps) ~prog:prog) spec_tab in
let spec_tab = List.fold_left spec_tab_add spec_tab
    [libcons;libnil;libreverse;] in
(* let spec_tab = add_spec spec_tab "Cons" ["h1";"t1";"l1"] ["u"; "v"]
 *     (E.And [
 *         (\* (E.Implies (list_order l1 u v,
 *          *             E.Or [E.And [list_member t1 v; int_eq h1 u]; list_order t1 u v])); *\)
 *         (list_head l1 h1);
 *         (\* (E.Implies (list_order t1 u v, list_order l1 u v)); *\)
 *         (E.Iff (list_member l1 u,
 *                 E.Or [list_member t1 u; int_eq h1 u]))
 *       ]) in
 * let spec_tab = add_spec spec_tab "Rev" ["l1";"l2"] ["u"; "v"]
 *     (E.And [
 *         (E.Iff (list_member l1 u, list_member l2 u))
 *       ]) in
 * let spec_tab = add_spec spec_tab "IsEmpty" ["l1"] ["u"]
 *     (E.Not (list_member l1 u)) in *)
let _ = printf "vc:\n%s\n" (vc_layout vc) in
let ctx =
  Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")] in
let _ = StrMap.iter (fun name spec ->
    printf "%s\n\n" (layout_spec_entry name spec)) spec_tab in
let axiom = Axiom.infer ~ctx:ctx ~vc:vc ~spectable:spec_tab ~dttp:T.IntList in
let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in
();;
