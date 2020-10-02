module Ast = Language.SpecAst
module Value = Pred.Value
module S = Solver;;
module A = Axiom.AxiomSyn.Syn;;

open Utils
open Z3
open Printf
open Language.Helper;;
open Ast
module SE = E.SE
;;
(* let rec insert x tree3 =
 *   match tree3 with
 *   | E -> T (E, x, E)
 *   | T (tree1, y, tree2) ->
 *     if Element.lt x y then T (insert x tree1, y, tree2)
 *     else if Element.lt y x then T (tree1, y, insert x tree2)
 *     else T (tree1, y, tree2) *)
let t l e r result = SpecApply ("T", [l;e;r;result]) in
let e tr = SpecApply ("E", [tr]) in
let insert_pre a t1 t2 = SpecApply ("InsertPre", [a;t1;t2]) in
let insert_post a t1 t2 = SpecApply ("InsertPost", [a;t1;t2]) in
let insert a t1 t2 = Implies (insert_pre a t1 t2, insert_post a t1 t2) in
let lt a b = SpecApply ("Lt", [a;b]) in
let vc =
  And [
    Implies (And [e tree3;e tree1; e tree2; t tree1 x tree2 tree5],
             insert x tree3 tree5);
    Implies (
      And [t tree1 x tree2 tree3;
           Ite (lt x y,
                And [insert x tree1 tree4; t tree4 y tree2 tree5],
                Ite (lt y x,
                     And [insert x tree2 tree4; t tree1 y tree4 tree5],
                     insert x tree3 tree5
                     (* t tree1 x tree2 tree5 *)
                    ))],
      insert x tree3 tree5
    );] in
(* let vc = Implies (
 *     And [t tree1 y tree2 tree3;lt x y;insert x tree1 tree4; t tree4 y tree2 tree5],
 *     insert x tree3 tree5
 *   ) in *)
(* let vc = Implies (
 *     And [t tree1 y tree2 tree3;lt y x;insert x tree2 tree4; t tree1 y tree4 tree5],
 *     insert x tree3 tree5
 *   ) in *)
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Lt" ["a";"b"] [] (int_lt a b) in
let spec_tab = add_spec spec_tab "InsertPre" ["x";"tree1";"tree2"] ["u"; "v"]
    (E.Implies (tree_any_order tree1 u v, Not (int_eq u v)))
in
let spec_tab = add_spec spec_tab "InsertPost" ["x";"tree1";"tree2"] ["u";"v"]
    (E.And [
        E.Implies (tree_any_order tree2 u v, Not (int_eq u v));
        E.Implies (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
      ])
in
let spec_tab = add_spec spec_tab "E" ["tree1"] ["u"]
    (Not (tree_member tree1 u)) in
let spec_tab = add_spec spec_tab "T" ["tree1";"x";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        E.Iff (
          tree_parent tree3 u v,
          E.Or [
            tree_parent tree1 u v;
            tree_parent tree2 u v;
            E.And [int_eq u x; E.Or [tree_member tree1 v; tree_member tree2 v]]
          ]
        );
        E.Iff (treep tree3 u v, E.And [tree_member tree1 u; tree_member tree2 v]);
        E.Iff (tree_member tree3 u,
                   E.Or [tree_member tree1 u; tree_member tree2 u; int_eq u x]);
        (* E.Implies (
         *   E.Or [tree_member tree1 u; tree_member tree2 u], tree_member tree3 u); *)
        tree_head tree3 x
      ]) in
let axiom = (["tree1"; "u"; "v"],
             E.And [
               E.Implies(
                 E.And [tree_head tree1 u; tree_member tree1 v],
                 tree_parent tree1 u v);
               (* E.Implies(tree_head tree1 u, tree_member tree1 u); *)
               E.Implies(tree_parent tree1 u v, E.And [tree_member tree1 u; tree_member tree1 v]);
             ]
            ) in
let _ = printf "vc:\n%s\n" (vc_layout vc) in
let ctx =
  Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")] in
let valid, _ = S.check ctx (to_z3 ctx (Not vc) spec_tab) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let valid, m = S.check ctx
    (Boolean.mk_and ctx [to_z3 ctx (Not vc) spec_tab;
                         E.forallformula_to_z3 ctx axiom
                        ]) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let _ = match m with
  | None -> printf "none.\n"
  | Some m -> printf "model:\n%s\n" (Model.to_string m) in
let _ = StrMap.iter (fun name spec ->
    printf "%s\n\n" (layout_spec_entry name spec)) spec_tab in
let _ = printf "axiom:\n%s\n" (E.pretty_layout_forallformula axiom) in
(* let axiom = A.axiom_infer ~ctx:ctx ~vc:vc ~spectable:spec_tab
 *     ~pred_names:["tree_member";"tree_left";"tree_right";"==";"tree_head"] ~dttp:E.SE.IntTree in
 * let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in *)
();;
