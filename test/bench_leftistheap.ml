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
(* let rec merge tree1 tree2 =
 *   match tree1, tree2 with
 *   | tree1, E -> tree1
 *   | E, tree2 -> tree2
 *   | T (rank1, x, a1, b1), T (rank2, y, a2, b2) ->
 *     if Elem.leq x y then makeT x a1 (merge b1 tree2)
 *     else makeT y a2 (merge tree1 b2) *)
open Language.Helper;;
let t rank x a b tr = SpecApply ("T", [rank;x;a;b;tr]) in
let e tr = SpecApply ("E", [tr]) in
let makeT x a b tr = SpecApply ("makeT", [x;a;b;tr]) in
let merge_pre tree1 tree2 tree3 = SpecApply ("MergePre", [tree1;tree2;tree3]) in
let merge_post tree1 tree2 tree3 = SpecApply ("MergePost", [tree1;tree2;tree3]) in
let le a b = SpecApply ("Le", [a;b]) in
let merge tree1 tree2 tree3 =
  Implies (merge_pre tree1 tree2 tree3, merge_post tree1 tree2 tree3) in
let rank1 = int_var "rank1" in
let rank2 = int_var "rank2" in
let a1, a2 = int_var "a1", int_var "a2" in
let b1, b2 = int_var "b1", int_var "b2" in
let tmp = tree_var "tree" in
(* let vc = And [
 *     Implies (e tree2, merge tree1 tree2 tree1);
 *     Implies (e tree1, merge tree1 tree2 tree2);
 *     Implies (
 *       And [t rank1 x a1 b1 tree1; t rank2 y a2 b2 tree2;
 *            Ite (le x y,
 *                 And [merge b1 tree2 tmp; makeT x a1 tmp tree3],
 *                 And [merge tree1 b2 tmp; makeT y a2 tmp tree3])],
 *       merge tree1 tree2 tree3)
 *   ]
 * in *)
let vc = Implies (
    And [t rank1 x a1 b1 tree1; t rank2 y a2 b2 tree2;le x y;
         merge b1 tree2 tmp; makeT x a1 tmp tree3],
    merge tree1 tree2 tree3) in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Le" ["a";"b"] [] (int_le a b) in
let spec_tab = add_spec spec_tab "MergePre" ["tree1";"tree2";"tree3"] ["u";"v"]
    (E.And [
        E.Implies (tree_parent tree1 u v, int_le u v);
        E.Implies (tree_parent tree2 u v, int_le u v);
      ]) in
let spec_tab = add_spec spec_tab "MergePost" ["tree1";"tree2";"tree3"] ["u";"v"]
    (E.And [E.Implies (tree_parent tree3 u v, int_le u v);
            E.Implies (member tree3 u, E.Or [member tree1 u; member tree2 u]);
            (* E.Iff (head tree3 u, E.Or [head tree1 u; head tree2 u]); *)
           ])
in
let spec_tab = add_spec spec_tab "E" ["tree1"] ["u"]
    (Not (member tree1 u)) in
let spec_tab = add_spec spec_tab "T" ["rank";"x";"tree1";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        (E.Implies (tree_parent tree3 u v,
                    E.Or [E.And [member tree1 v; int_eq x u];
                          E.And [member tree2 v; int_eq x u];
                          tree_parent tree1 u v;
                          tree_parent tree2 u v]));
        (head tree3 x);
        (E.Implies (E.Or [tree_parent tree1 u v;
                          tree_parent tree2 u v;], tree_parent tree3 u v));
        (E.Iff (member tree3 u,
                E.Or [member tree1 u; member tree2 u; int_eq x u]))
      ]) in
let spec_tab = add_spec spec_tab "makeT" ["x";"tree1";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        (E.Implies (tree_parent tree3 u v,
                    E.Or [E.And [member tree1 v; int_eq x u];
                          E.And [member tree2 v; int_eq x u];
                          tree_parent tree1 u v;
                          tree_parent tree2 u v]));
        (head tree3 x);
        (E.Implies (E.Or [tree_parent tree1 u v;
                          tree_parent tree2 u v;], tree_parent tree3 u v));
        (E.Iff (member tree3 u,
                E.Or [member tree1 u; member tree2 u; int_eq x u]))
      ]) in
let axiom = (["tree1"; "u"; "v"],
             E.And [
               E.Implies (E.And [head tree1 u; member tree1 v; E.Not (int_eq u v)],
                          tree_parent tree1 u v);
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
 *     ~pred_names:["member";"tree_left";"tree_right";"==";"head"] ~dttp:E.SE.IntTree in
 * let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in *)
();;
