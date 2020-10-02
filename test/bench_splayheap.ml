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
(* let rec partition pivot = function
 *   | E -> E, E
 *   | T (a, x, b) as tr ->
 *     if Elem.leq x pivot then
 *       match b with
 *       | E -> tr, E
 *       | T (b1, y, b2) ->
 *         if Elem.leq y pivot then
 *           let small, big = partition pivot b2 in
 *           T (T (a, x, b1), y, small), big
 *         else
 *           let small, big = partition pivot b1 in
 *           T (a, x, small), T (big, y, b2)
 *     else
 *       match a with
 *       | E -> E, tr
 *       | T (a1, y, a2) ->
 *         if Elem.leq y pivot then
 *           let small, big = partition pivot a2 in
 *           T (a1, y, small), T (big, x, b)
 *         else
 *           let small, big = partition pivot a1 in
 *           small, T (big, y, T (a2, x, b)) *)
let t l e r result = SpecApply ("T", [l;e;r;result]) in
let e result = SpecApply ("E", [result]) in
let le x y = SpecApply ("Le", [x;y]) in
let partition_pre a b c d = SpecApply ("PartitionPre", [a;b;c;d]) in
let partition_post a b c d = SpecApply ("PartitionPost", [a;b;c;d]) in
let partition a b c d = Implies (partition_pre a b c d, partition_post a b c d) in
let a, b, a1, a2, b1, b2 = map6 tree_var ("a", "b", "a1", "a2", "b1", "b2") in
let small, big, tr = map_triple tree_var ("small", "big", "tr") in
let tmp1, tmp2, tmp3, tmp4 = map4 tree_var ("tmp1", "tmp2", "tmp3", "tmp4") in
let pivot = int_var "pivot" in
let tmpe = tree_var "tmpe" in
let vc =
  And [
    Implies(e tr, partition pivot tr tr tr);
    Implies(t a x b tr,
            Ite(le x pivot,
                And[
                  Implies(e b, partition pivot tr tr b);
                  Implies(t b1 y b2 b,
                          Ite(le y pivot,
                              Implies(And[partition pivot b2 small big;
                                          t a x b1 tmp1; t tmp1 y small tmp2;],
                                      partition pivot tr tmp2 big),
                              Implies(And[partition pivot b1 small big;
                                          t a x small tmp1; t big y b2 tmp2;],
                                      partition pivot tr tmp1 tmp2)
                             )
                         )
                ],
                And[
                  Implies(e a, partition pivot tr a tr);
                  Implies(t a1 y a2 a,
                          Ite(le y pivot,
                              Implies(And[partition pivot a2 small big;
                                          t a1 y small tmp1; t big x b tmp2;],
                                      partition pivot tr tmp1 tmp2),
                              Implies(And[partition pivot a1 small big;
                                          t a2 x b tmp1; t big y tmp1 tmp2;],
                                      partition pivot tr small tmp2)
                             )
                         )
                ]
               )
           )
  ]
in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Le" ["x";"y"] [] (int_le x y) in
let spec_tab = add_spec spec_tab "PartitionPre" ["x";"tree1";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        E.Implies (treel tree1 u v, int_le v u);
        E.Implies (treer tree1 u v, int_le u v);
      ])
in
let spec_tab = add_spec spec_tab "PartitionPost" ["x";"tree1";"tree2";"tree3"] ["u";"v"]
    (E.And [
        E.Implies (treel tree2 u v, int_le v u);
        E.Implies (treer tree2 u v, int_le u v);
        E.Implies (treel tree3 u v, int_le v u);
        E.Implies (treer tree3 u v, int_le u v);
        E.Implies (tree_member tree2 u, int_le u x);
        E.Implies (tree_member tree3 u, int_le x u);
        E.Iff (tree_member tree1 u, Or[tree_member tree2 u; tree_member tree3 u]);
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
        E.Implies (tree_member tree1 v, int_eq v x);
        E.Implies (tree_member tree2 v, int_eq x v);
        E.Iff (treep tree3 u v, E.And [tree_member tree1 u; tree_member tree2 v]);
        E.Iff (tree_member tree3 u,
                   E.Or [tree_member tree1 u; tree_member tree2 u; int_eq u x]);
        tree_head tree3 x
      ]) in
let axiom = (["tree1"; "u"; "v"],
             E.And [
               E.Implies(
                 E.And [tree_head tree1 u; tree_member tree1 v],
                 tree_parent tree1 u v);
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
 *     ~pred_names:["tree_member";"treel";"treer";"==";"tree_head"] ~dttp:E.SE.IntTree in
 * let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in *)
();;
