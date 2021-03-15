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
open Language.Helper
open Bench_utils
open Frontend.Fast.Fast
;;
let testname = "splayhp" in
let ctx = init () in
let preds = ["tree_head"; "tree_member"; "tree_left"; "tree_right"; "tree_parallel"] in
let bpreds = ["=="] in
let tr, a1, a2, b1, b2, te = map6 tree_var ("tr", "a1", "a2", "b1", "b2", "te") in
let a, b = map_double tree_var ("a", "b") in
let tr1, tr2, tr3, tr4 = map4 tree_var ("tr1", "tr2", "tr3", "tr4") in
let small, big, nu =
  map_triple tree_var ("small", "big", "nu") in
let x1, x2, y1, y2, pivot = map5 int_var ("x1", "x2", "y1", "y2", "pivot") in
let nu_le1, nu_le2, nu_le3 = map_triple bool_var ("nu_le1", "nu_le2", "nu_le3") in
let nu_e1, nu_e2, nu_e3 = map_triple bool_var ("nu_e1", "nu_e2", "nu_e3") in
let e, e_hole = make_hole "e" [T.Bool; T.IntTree;] in
let t, t_hole = make_hole "t" [T.IntTree; T.Int; T.IntTree; T.IntTree;] in
let partition args =
  Implies (SpecApply ("PartitionPre", args), SpecApply ("PartitionPost", args)) in
let vc =
  Ast.Ite(e [nu_e1; tr;],
          Implies (e [booltrue; te], partition [pivot; te; te; te]),
          Implies(t [a; x; b; tr],
                  Ite(le [nu_le1; x; pivot;],
                      Ite(e [nu_e2; b;],
                          Implies (e [booltrue; te], partition [pivot; tr; tr; te]),
                          Implies (t [b1; y; b2; b],
                                   Ite(le [nu_le2; y; pivot;],
                                       Implies(
                                         And[partition [pivot; b2; small; big];
                                             t [a; x; b1; tr1]; t [tr1; y; small; tr2];],
                                         partition [pivot; tr; tr2; big]),
                                       Implies(
                                         And[partition [pivot; b1; small; big];
                                             t [a; x; small; tr1]; t [big; y; b2; tr2];],
                                         partition [pivot; tr; tr1; tr2])
                                      )
                                  )
                         ),
                      Ite(e [nu_e3; a;],
                          Implies (e [booltrue; te], partition [pivot; tr; te; tr]),
                          Implies (t [a1; y; a2; a],
                                   Ite(le [nu_le3; y; pivot;],
                                       Implies(And
                                                 [partition [pivot; a2; small; big];
                                                  t [a1; y; small; tr1]; t [big; x; b; tr2];],
                                               partition [pivot; tr; tr1; tr2]),
                                       Implies(And[partition [pivot; a1; small; big];
                                                   t [a2; x; b; tr1]; t [big; y; tr1; tr2];],
                                               partition [pivot; tr; small; tr2])
                                      )
                                  )
                         )
                     )
                 )
         )
in
let vcs = Ast.eliminate_cond vc in
let _ = List.map (fun vc -> printf "%s\n" (Ast.layout vc)) vcs in
let trace1_value = [
  "e", [V.B true; V.T Tree.Leaf; ];
] in
let trace2_value = [
  "e", [V.B false; V.T (Tree.Node (1, Tree.Leaf, Tree.Leaf)); ];
  "t", [V.T Tree.Leaf; V.I 1; V.T Tree.Leaf;
        V.T (Tree.Node (1, Tree.Leaf, Tree.Leaf));];
  "e", [V.B true; V.T Tree.Leaf; ]]
in
let spectable = predefined_spec_tab in
let holes = [e_hole; t_hole;] in
let traces = [trace1_value; trace2_value] in
let spectable = add_spec spectable "PartitionPre" ["x";"tr1";"tr2";"tr3"] ["u"; "v"]
    (E.And [
        E.Implies (E.And [treel tr1 u v], int_ge u v);
        E.Implies (E.And [treer tr1 u v], int_le u v);
      ]) in
let spectable = add_spec spectable "PartitionPost" ["x";"tr1";"tr2";"tr3"] ["u";]
    (
      E.And [
        E.Implies (E.And [tree_member tr2 u], int_le u x);
        E.Implies (E.And [tree_member tr3 u], int_ge u x);
      ]
    )
in
(* let _ = Printf.printf "vc=%s\n" (Ast.layout vc) in *)
let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
();;
