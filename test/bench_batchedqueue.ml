module Ast = Language.SpecAst
module Value = Pred.Value
module S = Solver;;
module A = Axiom.AxiomSyn.Syn;;

open Ast
open Utils
open Z3
open Printf
module SE = E.SE
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
let spec_tab = add_spec spec_tab "Cons" ["h1";"t1";"l1"] ["u"; "v"]
    (E.And [
        (* (E.Implies (list_order l1 u v,
         *             E.Or [E.And [list_member t1 v; int_eq h1 u]; list_order t1 u v])); *)
        (list_head l1 h1);
        (* (E.Implies (list_order t1 u v, list_order l1 u v)); *)
        (E.Iff (list_member l1 u,
                E.Or [list_member t1 u; int_eq h1 u]))
      ]) in
let spec_tab = add_spec spec_tab "Rev" ["l1";"l2"] ["u"; "v"]
    (E.And [
        (E.Iff (list_member l1 u, list_member l2 u))
      ]) in
let spec_tab = add_spec spec_tab "IsEmpty" ["l1"] ["u"]
    (E.Not (list_member l1 u)) in
let axiom = (["l1"; "u"; "v"],
             E.And [
               (* E.Implies (E.And [list_head l1 u; list_member l1 v; E.Not (int_eq u v)],
                *            list_order l1 u v); *)
               E.Implies (list_head l1 u, list_member l1 u);
               (* E.Implies (list_order l1 u v,
                *            E.And [list_member l1 u; list_member l1 v]);
                * E.Implies (E.And [list_member l1 u; list_member l1 v; E.Not (int_eq u v)],
                *            E.Or [list_order l1 u v; list_order l1 v u;]); *)
             ]
            ) in
let _ = printf "vc:\n%s\n" (vc_layout vc) in
let ctx =
  Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")] in
let valid, _ = S.check ctx (to_z3 ctx (Not vc) spec_tab) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let valid, _ = S.check ctx
    (Boolean.mk_and ctx [to_z3 ctx (Not vc) spec_tab;
                         E.forallformula_to_z3 ctx axiom
                        ]) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let _ = StrMap.iter (fun name spec ->
    printf "%s\n\n" (layout_spec_entry name spec)) spec_tab in
let _ = printf "axiom:\n%s\n" (E.pretty_layout_forallformula axiom) in
(* let axiom = A.axiom_infer ~ctx:ctx ~vc:vc ~spectable:spec_tab
 *     ~pred_names:["list_member";"list_order";"==";"list_head"] ~dttp:E.SE.IntList in
 * let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in *)
();;
