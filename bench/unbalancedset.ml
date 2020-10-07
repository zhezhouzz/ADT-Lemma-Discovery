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
let spec_tab = add_spec spec_tab "Insert" ["x";"tree1";"tree2"] ["u"]
    (E.And [
        E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
      ])
in
let axiom = assertion ctx (vc insert) spec_tab in
let _ = printf "axiom:\n\t%s\n" (E.pretty_layout_forallformula axiom) in

let insert tree1 tree2 tree3 = SpecApply ("Insert", [tree1;tree2;tree3]);
in
let spec_tab = add_spec spec_tab "Insert" ["x";"tree1";"tree2"] ["u"]
    (E.And [
        E.Implies(tree_member tree1 x,
                  E.Iff (tree_head tree1 u, tree_head tree2 u)
                 );
        E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
      ])
in
let axiom = assertion ctx (vc insert) spec_tab in
let _ = printf "axiom:\n\t%s\n" (E.pretty_layout_forallformula axiom) in
();;