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
let testname = "unbalancedset" in
(* let rec insert x tree3 =
 *   match tree3 with
 *   | E -> T (E, x, E)
 *   | T (tree1, y, tree2) ->
 *     if Element.lt x y then T (insert x tree1, y, tree2)
 *     else if Element.lt y x then T (tree1, y, insert x tree2)
 *     else T (tree1, y, tree2) *)
let ctx = init () in
let t l e r result = SpecApply ("T", [l;e;r;result]) in
let e tr = SpecApply ("E", [tr]) in
let lt a b = SpecApply ("Lt", [a;b]) in
let tree0 = tree_var "tree0" in
let tree1, tree2, tree3, tree4, tree5 =
  map5 tree_var ("tree1", "tree2", "tree3", "tree4", "tree5") in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Lt" ["a";"b"] [] (int_lt a b) in
let spec_tab, libt = register spec_tab
    {name = "T"; intps = [T.IntTree;T.Int;T.IntTree]; outtps = [T.IntTree];
     prog = function
       | [V.T l; V.I a; V.T r] -> [V.T (Tree.Node (a, l, r))]
       | _ -> raise @@ InterExn "bad prog"
    } in
let libt = add_spec spec_tab "T" ["tree0";"x";"tree1";"tree2"] ["u"; "v"]
  (And [
     Iff (tree_head tree2 u, int_eq x u);
     Iff (tree_member tree2 u, Or [treer tree2 x u; treer tree2 x u; tree_head tree2 u]);
     Iff (treel tree2 u v, Or [
         treel tree0  u v;
         treel tree1 u v;
         And [tree_head tree2 u; tree_member tree0 v];
       ]);
     Iff (treer tree2 u v, Or [
         treer tree0 u v;
         treer tree1 u v;
         And [tree_head tree2 u; tree_member tree0 v];
       ]);
     Iff (treep tree2 u v, Or [
         treep tree0 u v;
         treep tree1 u v;
         And [treel tree2 x u; treer tree2 x v];
       ]);
  ])
in
let spec_tab, libe = register spec_tab
    {name = "E"; intps = [T.IntTree;]; outtps = [T.Bool];
     prog = function
       | [V.T Tree.Leaf] -> [V.B true]
       | [V.T _] -> [V.B false]
       | _ -> raise @@ InterExn "bad prog"
    } in
let vc insert =
    (* Implies (And[t tree1 y tree2 tree3;
     *              lt x y;
     *              insert x tree2 tree4;
     *              t tree1 y tree4 tree5],
     *          insert x tree3 tree5)
     * in *)
  And [
    Implies (And [e tree3;e tree1; e tree2; t tree1 x tree2 tree5],
             insert x tree3 tree5);
    Implies (
      And [t tree1 y tree2 tree3;
           Ite (lt x y,
                And [insert x tree1 tree4; t tree4 y tree2 tree5],
                Ite (lt y x,
                     And [insert x tree2 tree4; t tree1 y tree4 tree5],
                     t tree1 y tree2 tree5
                    )
               )
          ],
      insert x tree3 tree5
    );
  ] in
let insert tree1 tree2 tree3 = SpecApply ("Insert", [tree1;tree2;tree3]) in
let preds = ["tree_head"; "tree_member"; "tree_left"; "tree_right"; "tree_parallel";
             "tree_node"
            ] in
let bpreds = ["=="] in
(* test *)
(* let spec_tab = add_spec spec_tab "Insert" ["x";"tree1";"tree2"] ["u"; "v"]
 *     (E.And [
 *         E.Implies(tree_member tree1 x,
 *                   E.Implies (treel tree1 u v, treel tree2 u v)
 *                  );
 *         E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
 *       ])
 * in
 * let axiom2 = assertion ctx (vc insert) spec_tab true in *)

let spec_tab = add_spec spec_tab "Insert" ["x";"tree1";"tree2"] ["u"]
    (E.And [
        E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
      ])
in
let axiom1 = assertion ctx (vc insert) spec_tab preds bpreds 1000 4 true testname "axiom1" in

let spec_tab = add_spec spec_tab "Insert" ["x";"tree1";"tree2"] ["u"; "v"]
    (E.And [
        E.Implies(tree_head tree1 x,
                  E.Implies (treel tree1 u v, treel tree2 u v)
                 );
        E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
      ])
in
let axiom2 = assertion ctx (vc insert) spec_tab preds bpreds 1000 4 true testname "axiom2" in

(* let spec_tab = add_spec spec_tab "Insert" ["x";"tree1";"tree2"] []
 *     (E.Not (tree_member tree2 x))
 * in
 * let axiom3 = assertion ctx (vc insert) spec_tab preds bpreds false testname "axiom3" in *)

let _ = to_verifier testname [axiom1;axiom2] in
();;
