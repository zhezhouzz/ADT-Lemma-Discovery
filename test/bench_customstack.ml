module Ast = Language.SpecAst
module Value = Preds.Pred.Value
module S = Solver;;
module A = Axiom.AxiomSyn.Syn;;

open Ast
open Utils
open Z3
open Printf
module SE = E.SE
;;
(* let rec concat l1 l2 =
 *   if is_empty l1 then l2
 *   else cons (stack_head l1) (concat (stack_tail l1) l2) *)
open Language.Helper;;
let cons h t l = SpecApply ("Cons", [h;t;l]) in
let is_empty l = SpecApply ("IsEmpty", [l]) in
let stack_head l h = SpecApply ("StackHead", [l;h]) in
let stack_tail l1 l2 = SpecApply ("StackTail", [l1;l2]) in
(* let concat_pre l1 l2 l3 = SpecApply ("ConcatPre", [l1;l2;l3]) in *)
let concat_post l1 l2 l3 = SpecApply ("ConcatPost", [l1;l2;l3]) in
let concat l1 l2 l3 = concat_post l1 l2 l3 in
let vc =
  Ite (is_empty l1,
       concat l1 l2 l2,
       Implies (And [stack_head l1 x; stack_tail l1 l3;
                     concat l3 l2 l4; cons x l4 l5;],
                concat l1 l2 l5)
      ) in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "ConcatPre" ["l1";"l2";"l3"] ["u";"v"] E.True in
let spec_tab = add_spec spec_tab "ConcatPost" ["l1";"l2";"l3"] ["u";"v"]
    (E.And [
        (* E.Implies (E.Or [list_order l1 u v;list_order l2 u v],
         *                list_order l3 u v); *)
            E.Iff (member l3 u, E.Or [member l1 u; member l2 u]);
           ])
in
let spec_tab = add_spec spec_tab "Cons" ["h1";"t1";"l1"] ["u"; "v"]
    (E.And [
        (E.Implies (list_order l1 u v,
                    E.Or [E.And [member t1 v; int_eq h1 u]; list_order t1 u v]));
        (head l1 h1);
        (E.Implies (list_order t1 u v, list_order l1 u v));
        (E.Iff (member l1 u,
                E.Or [member t1 u; int_eq h1 u]))
      ]) in
let spec_tab = add_spec spec_tab "StackHead" ["l1"; "x"] [] (head l1 x) in
let spec_tab = add_spec spec_tab "StackTail" ["l1"; "l2"] ["u";"v"]
    (E.And [
        E.Implies (list_order l1 u v, list_order l2 u v);
        E.Implies (E.Or [member l2 u], member l1 u);
      ]) in
let spec_tab = add_spec spec_tab "IsEmpty" ["l1"] ["u"]
    (E.Not (member l1 u)) in
let axiom = (["l1"; "u"; "v"],
             E.And [
               (* E.Implies (E.And [head l1 u; member l1 v; E.Not (int_eq u v)],
                *            list_order l1 u v); *)
               E.Implies (head l1 u, member l1 u);
               E.Implies (list_order l1 u v,
                          E.And [member l1 u; member l1 v]);
               E.Implies (E.And [member l1 u; member l1 v; E.Not (int_eq u v)],
                          E.Or [list_order l1 u v; list_order l1 v u;]);
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
 *     ~pred_names:["member";"list_order";"==";"head"] ~dttp:E.SE.IntList in
 * let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in *)
();;
