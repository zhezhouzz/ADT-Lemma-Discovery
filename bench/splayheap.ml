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
let testname = "splayhp" in
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
let ctx = init () in
let t l e r result = SpecApply ("T", [l;e;r;result]) in
let e result = SpecApply ("E", [result]) in
let le x y = SpecApply ("Le", [x;y]) in
let a, b, a1, a2, b1, b2 = map6 tree_var ("a", "b", "a1", "a2", "b1", "b2") in
let small, big, tr = map_triple tree_var ("small", "big", "tr") in
let tmp1, tmp2, tmp3, tmp4 = map4 tree_var ("tmp1", "tmp2", "tmp3", "tmp4") in
let tree0, tree1, tree2, tree3 = map4 tree_var ("tree0", "tree1","tree2","tree3") in
let pivot = int_var "pivot" in
let tmpe = tree_var "tmpe" in
let spec_tab = predefined_spec_tab in
let spec_tab = add_spec spec_tab "Le" ["x";"y"] [] (int_le x y) in
let spec_tab, libt = register spec_tab
    {name = "T"; intps = [T.IntTree;T.Int;T.IntTree]; outtps = [T.IntTree];
     prog = function
       | [V.T l; V.I a; V.T r] -> [V.T (Tree.Node (a, l, r))]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab = add_spec spec_tab "T" ["tree0";"x";"tree1";"tree2"] ["u"; "v"]
  (And [
     Iff (tree_head tree2 u, int_eq x u);
     Iff (tree_member tree2 u, Or [treel tree2 x u; treer tree2 x u; tree_head tree2 u]);
     Iff (treel tree2 u v, Or [
         treel tree0  u v;
         treel tree1 u v;
         And [tree_head tree2 u; tree_member tree0 v];
       ]);
     Iff (treer tree2 u v, Or [
         treer tree0 u v;
         treer tree1 u v;
         And [tree_head tree2 u; tree_member tree1 v];
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
let vc partition =
  Implies (e tree0,
  And [
    Implies(e tr, partition pivot tr tr tr);
    Implies(t a x b tr,
            Ite(le x pivot,
                And[
                  Implies(e b, partition pivot tr tr tree0);
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
                  Implies(e a, partition pivot tr tree0 tr);
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
          )
in
(* let vc partition =
 *   (\* Implies(And[t a x b tr;e b], partition pivot tr tr b) *\)
 *   (\* Implies(e tr, partition pivot tr tr tr); *\)
 *   partition pivot tree1 tree2 tree3
 * in *)
let preds = ["treeb_head"; "treeb_member"; "treeb_left"; "treeb_right"; "treeb_parallel";
             (* "treeb_node" *)
            ] in
let bpreds = ["=="] in

let partition a b c d = SpecApply ("Partition", [a;b;c;d]) in
let _ = print_vc_spec (vc partition) spec_tab in

let spec_tab = add_spec spec_tab "Partition" ["x";"tree1";"tree2";"tree3"] ["u"]
    (E.Iff (tree_member tree1 u, E.Or [tree_member tree2 u; tree_member tree3 u]))
in
let _ = printf_assertion spec_tab ["Partition"] in
let axiom1 = assertion ctx (vc partition) spec_tab
    ["tree_head"; "tree_member"; "tree_left"; "tree_right"; "tree_parallel";
     (* "tree_left" *)
    ]
    bpreds 110 6 true testname "1" in

let partition a b c d =
  Implies (SpecApply ("PartitionPre", [a;b;c;d]), SpecApply ("PartitionPost", [a;b;c;d])) in
let spec_tab = add_spec spec_tab "PartitionPre" ["x";"tree1";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        (* E.True *)
        E.Implies (E.And [treel tree1 u v], int_ge u v);
        E.Implies (E.And [treer tree1 u v], int_le u v);
      ]) in
let spec_tab = add_spec spec_tab "PartitionPost" ["x";"tree1";"tree2";"tree3"] ["u"; "v"]
    (
      E.And [
        E.Implies (E.And [tree_member tree2 u], int_le u x);
        E.Implies (E.And [tree_member tree3 u], int_ge u x);
      ]
    )
in
let _ = printf_assertion spec_tab ["PartitionPre";"PartitionPost"] in
let axiom2 = assertion ctx (vc partition) spec_tab
    ["tree_head"; "tree_member"; "tree_left"; "tree_right"; "tree_parallel";
    ]
    bpreds 115 6 true  testname "2" in

let spec_tab = add_spec spec_tab "PartitionPost" ["x";"tree1";"tree2";"tree3"] ["u"; "v"]
    (
      E.And [
        E.Implies (E.And [tree_member tree2 u], int_le u x);
        E.Implies (E.And [tree_member tree3 u], int_ge u x);
        E.Iff (tree_member tree1 u, E.Or [tree_member tree2 u; tree_member tree3 u])
      ]
    )
in
let _ = printf_assertion spec_tab ["PartitionPre";"PartitionPost"] in
let axiom3 = assertion ctx (vc partition) spec_tab
    ["tree_head"; "tree_member"; "tree_left"; "tree_right"; "tree_parallel";
    ]
    bpreds 100 7 true  testname "3" in
let _ = to_verifier testname [axiom1;axiom2;axiom3;] in
();;

