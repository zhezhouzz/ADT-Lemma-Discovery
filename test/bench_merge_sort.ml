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
(* Some simple literals to aid in test construction. *)
(* let libcode_cons a l = a :: l in
 * let rec libmerge l1 l2 =
 *   match l1, l2 with
 *   | [], l2 -> l2
 *   | l1, [] -> l1
 *   | h1 :: t1, h2 :: t2 ->
 *     if h1 <= h2
 *     then h1 :: (libmerge t1 l2)
 *     else h2 :: (libmerge l1 t2)
 * in *)
open Language.Helper;;
let cons h t l = SpecApply ("Cons", [h;t;l]) in
let merge_pre l1 l2 l3 = SpecApply ("MergePre", [l1;l2;l3]) in
let merge_post l1 l2 l3 = SpecApply ("MergePost", [l1;l2;l3]) in
let le a b = SpecApply ("Le", [a;b]) in
let merge l1 l2 l3 = Implies (merge_pre l1 l2 l3, merge_post l1 l2 l3) in
let vc = Implies (
    And [cons h1 t1 l1; cons h2 t2 l2;
         Ite (le h1 h2,
              And [merge t1 l2 ltmp0; cons h1 ltmp0 l3],
              And [merge l1 t2 ltmp0; cons h2 ltmp0 l3])],
    merge l1 l2 l3) in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Le" ["a";"b"] [] (int_le a b) in
let spec_tab = add_spec spec_tab "MergePre" ["l1";"l2";"l3"] ["u";"v"]
    (E.And [
        E.Implies (list_order l1 u v, int_le u v);
        E.Implies (list_order l2 u v, int_le u v);
      ]) in
let spec_tab = add_spec spec_tab "MergePost" ["l1";"l2";"l3"] ["u";"v"]
    (E.And [E.Implies (list_order l3 u v, int_le u v);
            E.Implies (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
            (* E.Iff (list_head l3 u, E.Or [list_head l1 u; list_head l2 u]); *)
           ])
in
let spec_tab = add_spec spec_tab "Cons" ["h1";"t1";"l1"] ["u"; "v"]
    (E.And [
        (E.Iff (list_order l1 u v,
                    E.Or [E.And [list_member t1 v; int_eq h1 u]; list_order t1 u v]));
        (E.Iff(list_head l1 u, int_eq u h1));
        (E.Implies (list_order t1 u v, list_order l1 u v));
        (E.Iff (list_member l1 u,
                E.Or [list_head l1 u; list_order l1 v u]
                  (* E.Or [list_member t1 u; int_eq h1 u] *)
               ))
      ]) in
(* (E.And [
 *     (E.Implies (list_order l1 u v,
 *                 E.Or [E.And [list_member t1 v; int_eq h1 u]; list_order t1 u v]));
 *     (list_head l1 h1);
 *     (E.Implies (list_order t1 u v, list_order l1 u v));
 *     (E.Iff (list_member l1 u,
 *             E.Or [list_member t1 u; int_eq h1 u]))
 *   ]) in *)
let axiom = (["l1"; "u"; "v"; "w"],
             E.And [
               E.Implies (E.And [list_head l1 u; list_member l1 v; E.Not (int_eq u v)],
                          list_order l1 u v);
               (* E.Implies (list_head l1 u, list_member l1 u); *)
               E.Implies (list_order l1 u v,
                          E.And [list_member l1 u; list_member l1 v]);
               E.Implies (E.And [list_member l1 u; list_member l1 v; E.Not (int_eq u v)],
                          E.Or [list_order l1 u v; list_order l1 v u;]);
             ]
            ) in
let ctx =
  Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")] in
let valid, _ = S.check ctx (to_z3 ctx (Not vc) spec_tab) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let valid, _ = S.check ctx
    (Boolean.mk_and ctx [to_z3 ctx (Not vc) spec_tab;
                         E.forallformula_to_z3 ctx axiom
                        ]) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
(* let axiom = A.axiom_infer ~ctx:ctx ~vc:vc ~spectable:spec_tab
 *     ~pred_names:["list_member";"list_order";"==";"list_head"] ~dttp:E.SE.IntList in
 * let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in *)
();;
