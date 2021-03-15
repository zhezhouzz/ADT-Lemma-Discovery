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
let testname = "rbset" in
let ctx = init () in
let preds = ["treeb_head"; "treeb_member"; "treeb_left"; "treeb_right"; "treeb_parallel"] in
let bpreds = ["=="] in
let tree1, tree2, tree3, a, b, c, d =
  map7 treei_var ("tree1", "tree2", "tree3", "a", "b", "c", "d") in
let te, nu, tmp1, tmp2, tmp3, tmp4 = map6 tree_var
    ("te", "nu", "tmp1", "tmp2", "tmp3", "tmp4") in
let r1, r2 = map_double bool_var ("r1", "r2") in
let x, y, rank1, rank2 = map4 int_var ("x", "y", "rank1", "rank2") in
let nu_e1, nu_e2, nu_le = map_triple bool_var ("nu_e1", "nu_e2", "nu_le") in
let e, e_hole = make_hole "e" [T.Bool; T.IntTreeB;] in
let t, t_hole = make_hole "t" [T.Bool; T.IntTreeB; T.Int; T.IntTreeB; T.IntTreeB;] in
let red r = SpecApply ("R", r) in
let black r = SpecApply ("B", r) in
let redb r = E.Atom(SE.Op (T.Bool, "==", [r;SE.Literal (T.Bool, SE.L.Bool true)])) in
let blackb r = E.Not(redb r) in
let spectable = predefined_spec_tab in
let spectable = add_spec spectable "R" ["a"] [] (redb a) in
let spectable = add_spec spectable "B" ["a"] [] (blackb a) in
let balance args =
  Implies (SpecApply ("BalancePre", args), SpecApply ("BalancePost", args)) in
let vcs =
  let precond = And [black [r1]; red [r2]; e [booltrue;te;];] in
  let bodys =
    [
            Implies(And [t [r2;a;x;b;tmp1]; t [r2;tmp1;y;c;tree1];
                         t [r1;a;x;b;tmp2]; t [r1;c;z;d;tmp3]; t[r2;tmp2;y;tmp3;tmp4];],
                    balance [r1;tree1;z;d;tmp4]);
            Implies(And [t [r2;b;y;c;tmp1]; t[r2;te;x;tmp1;tree1];
                         t [r1;te;x;b;tmp2]; t [r1;c;z;d;tmp3]; t [r2;tmp2;y;tmp3;tmp4];],
                    balance[r1;tree1;z;d;tmp4]);
            Implies(And [t [r2;te;x;te;tree1];
                         t [r2;tree1;z;d;tmp4];],
                    balance[r1;tree1;z;d;tmp4]);
            Implies(And [t [r2;b;y;c;tmp1]; t [r2;tmp1;z;d;tree2];
                         t [r1;te;x;b;tmp2]; t [r1;c;z;d;tmp3]; t[r2;tmp2;y;tmp3;tmp4];],
                    balance[r1;te;x;tree2;tmp4]);
            Implies(And [t [r2;c;z;d;tmp1]; t [r2;te;y;tmp1;tree2];
                         t [r1;te;x;te;tmp2]; t [r1;c;z;d;tmp3]; t [r2;tmp2;y;tmp3;tmp4];],
                    balance[r1;te;x;tree2;tmp4]);
            Implies(And [t [r2;te;x;te;tmp4];],
                    balance[r1;te;x;te;tmp4]);
            Implies(And [t [r1;b;x;d;tmp4];],
                    balance[r1;b;x;d;tmp4]);
          ]
  in
  List.map (fun body -> Implies(precond, body)) bodys
in
let _ = List.map (fun vc -> printf "%s\n" (Ast.layout vc)) vcs in
let trace1_value = [
  "e", [V.B true; V.TB LT.Leaf; ];
] in
let trace2_value = [
  "e", [V.B false; V.TB (LT.Node (true, 1, LT.Leaf, LT.Leaf)); ];
  "t", [V.B true; V.TB LT.Leaf; V.I 1; V.TB LT.Leaf;
        V.TB (LT.Node (true, 1, LT.Leaf, LT.Leaf))];
  "t", [V.B true; V.TB LT.Leaf; V.I 1;
        V.TB (LT.Node (true, 1, LT.Leaf, LT.Leaf));
        V.TB (LT.Node (true, 1, LT.Leaf,
                                LT.Node (true, 1, LT.Leaf, LT.Leaf)));
       ];
]
in
let holes = [e_hole; t_hole] in
let traces = [trace1_value; trace2_value] in
let spectable = add_spec spectable "BalancePre" ["r1";"tree1";"x";"tree2";"tree3"] []
    (E.True) in
let spectable = add_spec spectable "BalancePost" ["r1";"tree1";"x";"tree2";"tree3"] ["u"]
    (E.And [
        E.Iff (treeb_member tree3 u,
               E.Or [treeb_member tree1 u; treeb_member tree2 u; int_eq u x]
              );
      ])
in
let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
let spectable = add_spec spectable "BalancePre" ["r1";"tree1";"x";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        E.Implies (treeb_any_order tree1 u v, Not (int_eq u v));
        E.Implies (treeb_any_order tree2 u v, Not (int_eq u v));
        E.Implies (E.And [treeb_member tree1 u; treeb_member tree1 v],
                   Not (int_eq u v));
        E.Implies (E.Or[treeb_member tree1 u; treeb_member tree2 u], Not (int_eq u x));
      ])
in
let spectable = add_spec spectable "BalancePost" ["r1";"tree1";"x";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        (* tree_once tree3 u; *)
        (* E.Implies(tree_member tree3 u, tree_once tree3 u); *)
        E.Implies (treeb_any_order tree3 u v, Not (int_eq u v));
        E.Iff (treeb_member tree3 u,
               E.Or [treeb_member tree1 u; treeb_member tree2 u; int_eq u x]
              );
      ])
in
let _ = test ctx vcs spectable holes preds bpreds 2 2 traces in
();;
