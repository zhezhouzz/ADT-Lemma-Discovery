module Ast = Language.SpecAst
module Value = Preds.Pred.Value
module S = Solver;;
module A = Axiom.AxiomSyn.Syn;;

open Utils
open Z3
open Printf
open Language.Helper;;
open Ast
module SE = E.SE
;;
(* let rec insert x = function
 *   | E -> T (E, x, E)
 *   | T (a, y, b) as s ->
 *     if Element.lt x y then T (insert x a, y, b)
 *     else if Element.lt y x then T (a, y, insert x b)
 *     else s *)
let t l e r result = SpecApply ("T", [l;e;r;result]) in
let insert_pre a t1 t2 = SpecApply ("InsertPre", [a;t1;t2]) in
let insert_post a t1 t2 = SpecApply ("InsertPost", [a;t1;t2]) in
let insert a t1 t2 = Implies (insert_pre a t1 t2, insert_post a t1 t2) in
let lt a b = SpecApply ("Lt", [a;b]) in
(* let vc = Implies (
 *     And [t tree1 x tree2 tree3;
 *          Ite (lt x y,
 *               And [insert x tree1 tree4; t tree4 y tree2 tree5],
 *               Ite (lt y x,
 *                    And [insert x tree2 tree4; t tree1 y tree4 tree5],
 *                    insert x tree3 tree5
 *                    (\* t tree1 x tree2 tree5 *\)
 *                   ))],
 *     insert x tree3 tree5
 *   ) in *)
let vc = Implies (
    And [t tree1 y tree2 tree3;lt x y;insert x tree1 tree4; t tree4 y tree2 tree5],
    insert x tree3 tree5
  ) in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Lt" ["a";"b"] [] (int_lt a b) in
let spec_tab = add_spec spec_tab "InsertPre" ["x";"tree1";"tree2"] ["u"; "v"]
    (E.Implies (tree_parent tree1 u v, int_ge u v))
in
let spec_tab = add_spec spec_tab "InsertPost" ["x";"tree1";"tree2"] ["u";"v"]
    (E.And [
        E.Implies (tree_parent tree2 u v, int_ge u v);
        E.Implies (member tree2 u, E.Or [member tree1 u; int_eq u x]);
      ])
in
let spec_tab = add_spec spec_tab "T" ["tree1";"x";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        E.Implies (
          tree_parent tree3 u v,
          E.Or [
            tree_parent tree1 u v;
            tree_parent tree2 u v;
            E.And [int_eq u x; E.Or [member tree1 v; member tree2 v]]
          ]
        );
        E.Implies (
          E.Or [
            tree_parent tree1 u v;
            tree_parent tree2 u v;
          ],
          tree_parent tree3 u v
          (* E.And [int_eq u x; E.Or [member tree1 v; member tree2 v]] *)
        );
        E.Iff (member tree3 u,
                   E.Or [member tree1 u; member tree2 u; int_eq u x]);
        (* E.Implies (
         *   E.Or [member tree1 u; member tree2 u], member tree3 u); *)
        head tree3 x
      ]) in
let axiom = (["tree1"; "u"; "v"],
             E.And [
               E.Implies(
                 E.And [head tree1 u; Not (int_eq u v); member tree1 v],
                 tree_parent tree1 u v);
               (* E.Implies(head tree1 u, member tree1 u); *)
             ]
            ) in
let _ = printf "vc:%s\n" (layout vc) in
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
let axiom = A.axiom_infer ~ctx:ctx ~vc:vc ~spectable:spec_tab
    ~pred_names:["member";"tree_left";"tree_right";"==";"head"] ~dttp:E.SE.IntTree in
let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in
();;
