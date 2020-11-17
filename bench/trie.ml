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
let testname = "trie" in
(* let rec ins default i a m =
 *   match m with
 *   | Trie.Leaf ->
 *     (match i with
 *      | [] -> Trie.Node(Trie.Leaf, a, Trie.Leaf)
 *      | z :: i' ->
 *        if z > 0
 *        then Trie.Node(ins default i' a Trie.Leaf, default, Trie.Leaf)
 *        else Trie.Node(Trie.Leaf, default, ins default i' a Trie.Leaf)
 *     )
 *   | Trie.Node(l, y, r) ->
 *     (match i with
 *      | [] -> Trie.Node(l, a, r)
 *      | z :: i' ->
 *        if z > 0
 *        then Trie.Node(ins default i' a l, y, r)
 *        else Trie.Node(l, y, ins default i' a r)
 *     ) *)
let ctx = init () in
let t l e r result = SpecApply ("TrieT", [l;e;r;result]) in
let e tr = SpecApply ("TrieE", [tr]) in
let lt a b = SpecApply ("Lt", [a;b]) in
let tree0 = tree_var "tree0" in
let tree1, tree2, tree3, tree4, tree5 =
  map5 tree_var ("tree1", "tree2", "tree3", "tree4", "tree5") in
let tree6, tree7 = map_double tree_var ("tree6", "tree7") in
let l1, l2 = map_double list_var ("l1", "l2") in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Lt" ["a";"b"] [] (int_lt a b) in
let spec_tab, cons = register spec_tab
    {name = "Cons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.I h; V.L t] -> [V.L (h :: t)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, is_empty = register spec_tab
    {name = "IsEmpty"; intps = [T.IntList]; outtps = [T.Bool];
     prog = function
       | [V.L []] -> [V.B false]
       | [V.L _] -> [V.B true]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, libt = register spec_tab
    {name = "TrieT"; intps = [T.IntTree;T.Int;T.IntTree]; outtps = [T.IntTree];
     prog = function
       | [V.T l; V.I a; V.T r] -> [V.T (Tree.Node (a, l, r))]
       | _ -> raise @@ InterExn "bad prog"
    } in
(* let spec_tab = add_spec spec_tab "T" ["tree0";"x";"tree1";"tree2"] ["u"; "v"]
 *     (And [
 *         Iff (tree_head tree2 u, int_eq x u);
 *         Iff (tree_member tree2 u, Or [treel tree2 x u; treer tree2 x u; tree_head tree2 u]);
 *         Iff (treel tree2 u v, Or [
 *             treel tree0  u v;
 *             treel tree1 u v;
 *             And [tree_head tree2 u; tree_member tree0 v];
 *           ]);
 *         Iff (treer tree2 u v, Or [
 *             treer tree0 u v;
 *             treer tree1 u v;
 *             And [tree_head tree2 u; tree_member tree1 v];
 *           ]);
 *         Iff (treep tree2 u v, Or [
 *             treep tree0 u v;
 *             treep tree1 u v;
 *             And [treel tree2 x u; treer tree2 x v];
 *           ]);
 *       ])
 * in *)
let spec_tab, libe = register spec_tab
    {name = "TrieE"; intps = [T.IntTree;]; outtps = [T.Bool];
     prog = function
       | [V.T Tree.Leaf] -> [V.B true]
       | [V.T _] -> [V.B false]
       | _ -> raise @@ InterExn "bad prog"
    } in
let vc ins =
  Implies(e tree0,
          And [
            Implies (e tree1,
                     And[
                       Implies (And[is_empty [l1]; t tree0 y tree0 tree3], ins x l1 y tree1 tree3);
                       Implies (cons [z; l2; l1],
                                Ite (lt z const0,
                                     Implies (
                                       And [ins x l2 y tree0 tree3;
                                            t tree3 x tree0 tree4
                                           ], ins x l1 y tree1 tree4),
                                     Implies (
                                       And [ins x l2 y tree0 tree3;
                                            t tree0 x tree3 tree4
                                           ], ins x l1 y tree1 tree4)
                                    )
                               )
                     ]
                    );
            Implies (t tree5 y tree6 tree1,
                     And[
                       Implies (And[is_empty [l1]; t tree5 x tree6 tree7],
                                ins x l1 y tree1 tree7);
                       Implies (cons [z; l2; l1],
                                Ite (lt z const0,
                                     Implies (
                                       And [ins x l2 y tree5 tree3;
                                            t tree3 y tree6 tree4
                                           ], ins x l1 y tree1 tree4),
                                     Implies (
                                       And [ins x l2 y tree6 tree3;
                                            t tree5 y tree3 tree4
                                           ], ins x l1 y tree1 tree4)
                                    )
                               )
                     ]
                    )
          ]
         )
in
let ins x l1 y tree1 tree2 = SpecApply ("Ins", [x;l1;y;tree1;tree2]) in
let _ = print_vc_spec (vc ins) spec_tab in
let preds = ["tree_head"; "tree_member"; "tree_left"; "tree_right"; "tree_parallel";
            ] in
let bpreds = ["=="] in

let spec_tab = add_spec spec_tab "Ins" ["x";"l1";"y";"tree1";"tree2"] ["u"]
    (E.And [
        E.Implies (tree_member tree2 u, Or [tree_member tree1 u; int_eq u y; int_eq u x]);
        (* E.Implies (Or [tree_member tree1 u; int_eq u y; int_eq u x], tree_member tree2 u); *)
      ])
in
(* let _ = printf_assertion spec_tab ["Ins"] in *)
let axiom1 = assertion ctx (vc ins) spec_tab preds bpreds 340 5 true testname "axiom1" in

let _ = to_verifier testname [axiom1] in
();;
