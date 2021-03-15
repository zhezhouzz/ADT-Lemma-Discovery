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
let testname = "unbset" in
let ctx = init () in
let preds = ["tree_head"; "tree_member"; "tree_left"; "tree_right"; "tree_parallel"] in
let bpreds = ["=="] in
let tree1, tree2, tree3, a1, a2, b1, b2 =
  map7 treei_var ("tree1", "tree2", "tree3", "a1", "a2", "b1", "b2") in
let te, nu, nu_insert = map_triple tree_var ("te", "nu", "nu_insert") in
let x, y, rank1, rank2 = map4 int_var ("x", "y", "rank1", "rank2") in
let nu_e, nu_lt1, nu_lt2 = map_triple bool_var ("nu_e1", "nu_e2", "nu_le") in
let e, e_hole = make_hole "e" [T.Bool; T.IntTree;] in
let t, t_hole = make_hole "t" [T.IntTree; T.Int; T.IntTree; T.IntTree;] in
let insert args =
  Implies (SpecApply ("InsertPre", args), SpecApply ("InsertPost", args)) in
let vc =
  Ast.Ite(e [nu_e; tree3;],
          Implies(And [e [booltrue; te];
                       t [te;x;te;nu]],
                  insert [x; tree3; nu]),
          Implies(t [tree1;y;tree2;tree3],
                  Ite(lt [nu_lt1;x;y],
                      Implies(And [insert [x;tree1;nu_insert];
                                   t [nu_insert;y;tree2;nu]],
                              insert [x; tree3; nu]),
                      Ite(lt [nu_lt2;y;x],
                          Implies(And [insert [x;tree2;nu_insert];
                                       t [tree1;y;nu_insert;nu]],
                                  insert [x; tree3; nu]),
                          Implies(t [tree1;y;tree2;nu],
                                 insert [x; tree3; nu])
                         )
                     )
                 )
         )
in
let vcs = Ast.eliminate_cond vc in
let _ = List.map (fun vc -> printf "%s\n" (Ast.layout vc)) vcs in
let trace1_value = [
  "e", [V.B true; V.T Tree.Leaf;];
  "t", [V.T Tree.Leaf; V.I 1; V.T Tree.Leaf;
        V.T (Tree.Node (1, Tree.Leaf, Tree.Leaf))];
] in
let trace2_value = [
  "t", [V.T Tree.Leaf; V.I 1; V.T Tree.Leaf;
        V.T (Tree.Node (1, Tree.Leaf, Tree.Leaf))];
  "t", [V.T Tree.Leaf; V.I 1; V.T (Tree.Node (2, Tree.Leaf, Tree.Leaf));
        V.T (Tree.Node (1, Tree.Leaf, Tree.Node (2, Tree.Leaf, Tree.Leaf)))]
]
in
let spectable = predefined_spec_tab in
let holes = [e_hole; t_hole] in
let traces = [trace1_value; trace2_value] in
let spectable = add_spec spectable "InsertPre" ["x";"tree1";"tree2"] []
    (E.True) in
let spectable = add_spec spectable "InsertPost" ["x";"tree1";"tree2"] ["u"]
    (E.And [
        E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
      ])
in
let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
let spectable = add_spec spectable "InsertPost" ["x";"tree1";"tree2"] ["u"; "v"]
    (E.And [
        E.Implies(tree_head tree1 x,
                  E.Implies (treel tree1 u v, treel tree2 u v)
                 );
        E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
      ])
in
let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
();;
