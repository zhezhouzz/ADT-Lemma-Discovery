module Ast = Language.SpecAst
module Value = Pred.Value
module SpecAbd = Inference.SpecAbduction;;

open Ast
open Utils
open Z3
open Printf
module SE = E.SE
module T = Tp.Tp
module V = Pred.Value
module LT = LabeledTree
open Language.Helper
open Bench_utils
open Frontend.Fast.Fast
;;
let testname = "leftisthp" in
let ctx = init () in
let preds = ["treei_head"; "treei_member"; "treei_left"; "treei_right"; "treei_parallel"] in
let bpreds = ["=="] in
let tree1, tree2, tree3, a1, a2, b1, b2 =
  map7 treei_var ("tree1", "tree2", "tree3", "a1", "a2", "b1", "b2") in
let te, nu, tmp1 = map_triple tree_var ("te", "nu", "tmp1") in
let x, y, rank1, rank2 = map4 int_var ("x", "y", "rank1", "rank2") in
let nu_e1, nu_e2, nu_le = map_triple bool_var ("nu_e1", "nu_e2", "nu_le") in
let e, e_hole = make_hole "e" [T.Bool; T.IntTreeI;] in
let t, t_hole = make_hole "t" [T.Int; T.Int; T.IntTreeI; T.IntTreeI; T.IntTreeI;] in
let makeT, makeT_hole = make_hole "makeT" [T.Int; T.IntTreeI; T.IntTreeI; T.IntTreeI;] in
let merge args =
  Implies (SpecApply ("MergePre", args), SpecApply ("MergePost", args)) in
let vc =
  Ast.Ite(e [nu_e2; tree2;],
          merge [tree1; tree2; tree1],
          Ite(e [nu_e1; tree1],
              merge [tree1; tree2; tree2],
              Implies (And [t [rank1;x;a1;b1;tree1]; t [rank2;y;a2;b2;tree2]],
                       Ite(le [nu_le;x;y],
                           Implies(And[
                               merge [b1;tree2;tmp1]; makeT [x;a2;tmp1;nu]],
                                   merge [tree1; tree2; nu]
                             ),
                           Implies(And[
                               merge [tree1;b2;tmp1]; makeT [y;a2;tmp1;nu]],
                                   merge [tree1; tree2; nu]
                             ))
                          )
                      )
         )
    in
let vcs = Ast.eliminate_cond vc in
let _ = List.map (fun vc -> printf "%s\n" (Ast.layout vc)) vcs in
let trace1_value = [
  "e", [V.B true; V.TI LT.Leaf; ];
] in
let trace2_value = [
  "e", [V.B false; V.TI (LT.Node (1, 1, LT.Leaf, LT.Leaf)); ];
  "t", [V.I 0; V.I 1; V.TI LT.Leaf; V.TI LT.Leaf;
        V.TI (LT.Node (1, 1, LT.Leaf, LT.Leaf))];
  "t", [V.I 1; V.I 1; V.TI LT.Leaf;
        V.TI (LT.Node (1, 1, LT.Leaf, LT.Leaf));
        V.TI (LT.Node (2, 1, LT.Leaf,
                                LT.Node (1, 1, LT.Leaf, LT.Leaf)));
       ];
  "makeT", [V.I 1; V.TI LT.Leaf;
            V.TI (LT.Node (2, 1, LT.Leaf,
                                    LT.Node (1, 1, LT.Leaf, LT.Leaf)));
            V.TI (LT.Node (1, 1,
                  LT.Node (2, 1, LT.Leaf,
                           LT.Node (1, 1, LT.Leaf, LT.Leaf)),
                  LT.Leaf
            ))
           ];
]
in
let spectable = predefined_spec_tab in
let holes = [e_hole; t_hole; makeT_hole] in
let traces = [trace1_value; trace2_value] in
let spectable = add_spec spectable "MergePre" ["tree1";"tree2";"tree3"] []
    (E.True) in
let spectable = add_spec spectable "MergePost" ["tree1";"tree2";"tree3"] ["u"]
    (E.And [
        (E.Iff (treei_member tree3 u, E.Or [treei_member tree1 u; treei_member tree2 u]));
      ])

in
let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
let spectable = add_spec spectable "MergePost" ["tree1";"tree2";"tree3"] ["u"]
    (E.And [
        E.Implies (treei_head tree3 u,
                   E.Or [treei_head tree1 u; treei_head tree2 u;]);
        (E.Iff (treei_member tree3 u, E.Or [treei_member tree1 u; treei_member tree2 u]));
      ])

in
let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
();;
