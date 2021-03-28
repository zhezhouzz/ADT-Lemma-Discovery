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
let bpreds = ["=="] in
let tree1, tree2, tree3, a, b, c, d =
  map7 treei_var ("tree1", "tree2", "tree3", "a", "b", "c", "d") in
let te, nu, tmp1, tmp2, tmp3, tmp4 = map6 tree_var
    ("te", "nu", "tmp1", "tmp2", "tmp3", "tmp4") in
let r, r1, r2 = map_triple bool_var ("r", "r1", "r2") in
let x, y, rank1, rank2 = map4 int_var ("x", "y", "rank1", "rank2") in
let nu_e1, nu_e2, nu_le = map_triple bool_var ("nu_e1", "nu_e2", "nu_le") in
let t, t_hole = make_hole_from_info
    {name = "t"; intps = [T.Bool; T.IntTreeB; T.Int; T.IntTreeB];
     outtps = [T.IntTreeB];
     prog = function
       | [V.B r; V.TB a; V.I x; V.TB b] -> Some [V.TB (LabeledTree.Node(r,x,a,b))]
       | _ -> raise @@ InterExn "bad prog"
    } in
let e, e_hole = make_hole_from_info
    {name = "e"; intps = []; outtps = [T.IntTreeB];
     prog = function
       | [] -> Some [V.TB LabeledTree.Leaf]
       | _ -> raise @@ InterExn "bad prog"
    } in
let red r = SpecApply ("R", r) in
let black r = SpecApply ("B", r) in
let redb r = E.Atom(SE.Op (T.Bool, "==", [r;SE.Literal (T.Bool, SE.L.Bool true)])) in
let blackb r = E.Not(redb r) in
let spectable = predefined_spec_tab in
let predefined_spec_tab = add_spec predefined_spec_tab "R" [T.Bool, "a"] [] (redb a) in
let predefined_spec_tab = add_spec predefined_spec_tab "B" [T.Bool, "a"] [] (blackb a) in
let balance args =
  Implies (SpecApply ("BalancePre", args), SpecApply ("BalancePost", args)) in
let pre =
  Ast.make_match [T.Bool, "r"; T.IntTreeB, "tree1"; T.Int, "x"; T.IntTreeB, "tree2";]
    [T.IntTreeB, "tree3"]
    [
      (Some (And [black [r1]; red [r2]; e [te;];
               t [r2;a;x;b;tmp1];t [r2;tmp1;y;c;tree1];]),
       [T.Bool, "r1"; T.IntTreeB, "tree1"; T.Int, "z"; T.IntTreeB, "d";]),
      (Some (And [t [r1;a;x;b;tmp2]; t [r1;c;z;d;tmp3]; t[r2;tmp2;y;tmp3;tmp4];]),
       [(T.IntTree, "tmp4");]);
      (Some (And [black [r1]; red [r2]; e [te;];
                  t [r2;b;y;c;tmp1]; t[r2;te;x;tmp1;tree1];]),
       [T.Bool, "r1"; T.IntTreeB, "tree1"; T.Int, "z"; T.IntTreeB, "d";]),
      (Some (And [t [r1;te;x;b;tmp2]; t [r1;c;z;d;tmp3]; t [r2;tmp2;y;tmp3;tmp4];]),
       [(T.IntTree, "tmp4");]);
      (Some (And [black [r1]; red [r2]; e [te;];
                  t [r2;te;x;te;tree1];]),
       [T.Bool, "r1"; T.IntTreeB, "tree1"; T.Int, "z"; T.IntTreeB, "d";]),
      (Some (And [t [r2;tree1;z;d;tmp4];]),
       [(T.IntTree, "tmp4");]);
      (Some (And [black [r1]; red [r2]; e [te;];
                  t [r2;b;y;c;tmp1]; t [r2;tmp1;z;d;tree2];]),
       [T.Bool, "r1"; T.IntTreeB, "te"; T.Int, "x"; T.IntTreeB, "tree2";]),
      (Some (And [t [r1;te;x;b;tmp2]; t [r1;c;z;d;tmp3]; t[r2;tmp2;y;tmp3;tmp4];]),
       [(T.IntTree, "tmp4");]);
      (Some (And [black [r1]; red [r2]; e [te;];
                  t [r2;c;z;d;tmp1]; t [r2;te;y;tmp1;tree2];]),
       [T.Bool, "r1"; T.IntTreeB, "te"; T.Int, "x"; T.IntTreeB, "tree2";]),
      (Some (And [t [r1;te;x;te;tmp2]; t [r1;c;z;d;tmp3]; t [r2;tmp2;y;tmp3;tmp4];]),
       [(T.IntTree, "tmp4");]);
      (Some (And [black [r1]; red [r2]; e [te;];
                  ]),
       [T.Bool, "r1"; T.IntTreeB, "te"; T.Int, "x"; T.IntTreeB, "te";]),
      (Some (t [r2;te;x;te;tmp4];),
       [(T.IntTree, "tmp4");]);
      (Some (And [black [r1]; red [r2]; e [te;];
                 ]),
       [T.Bool, "r1"; T.IntTreeB, "b"; T.Int, "x"; T.IntTreeB, "d";]),
      (Some (t [r1;b;x;d;tmp4];),
       [(T.IntTree, "tmp4");]);
    ]
in
(* let vcs =
 *   let precond = And [black [r1]; red [r2]; e [booltrue;te;];] in
 *   let bodys =
 *     [
 *             Implies(And [t [r2;a;x;b;tmp1]; t [r2;tmp1;y;c;tree1];
 *                          t [r1;a;x;b;tmp2]; t [r1;c;z;d;tmp3]; t[r2;tmp2;y;tmp3;tmp4];],
 *                     balance [r1;tree1;z;d;tmp4]);
 *             Implies(And [t [r2;b;y;c;tmp1]; t[r2;te;x;tmp1;tree1];
 *                          t [r1;te;x;b;tmp2]; t [r1;c;z;d;tmp3]; t [r2;tmp2;y;tmp3;tmp4];],
 *                     balance[r1;tree1;z;d;tmp4]);
 *             Implies(And [t [r2;te;x;te;tree1];
 *                          t [r2;tree1;z;d;tmp4];],
 *                     balance[r1;tree1;z;d;tmp4]);
 *             Implies(And [t [r2;b;y;c;tmp1]; t [r2;tmp1;z;d;tree2];
 *                          t [r1;te;x;b;tmp2]; t [r1;c;z;d;tmp3]; t[r2;tmp2;y;tmp3;tmp4];],
 *                     balance[r1;te;x;tree2;tmp4]);
 *             Implies(And [t [r2;c;z;d;tmp1]; t [r2;te;y;tmp1;tree2];
 *                          t [r1;te;x;te;tmp2]; t [r1;c;z;d;tmp3]; t [r2;tmp2;y;tmp3;tmp4];],
 *                     balance[r1;te;x;tree2;tmp4]);
 *             Implies(And [t [r2;te;x;te;tmp4];],
 *                     balance[r1;te;x;te;tmp4]);
 *             Implies(And [t [r1;b;x;d;tmp4];],
 *                     balance[r1;b;x;d;tmp4]);
 *           ]
 *   in
 *   List.map (fun body -> Implies(precond, body)) bodys
 * in *)
let post = balance [r;tree1;x;tree2;tree3] in
let elems = [T.Int, "x"; T.Int, "y"] in
let holel = [
  e_hole;
  t_hole
] in
let spectable = add_spec predefined_spec_tab "BalancePre"
    [T.Bool, "r1"; T.IntTreeB, "tree1"; T.Int, "x"; T.IntTreeB, "tree2";T.IntTreeB, "tree3"]
    []
    (E.True) in
let spectable = add_spec spectable "BalancePost"
    [T.Bool, "r1"; T.IntTreeB, "tree1"; T.Int, "x"; T.IntTreeB, "tree2";T.IntTreeB, "tree3"]
    [T.Int, "u"]
    (E.And [
        E.Iff (treeb_member tree3 u,
               E.Or [treeb_member tree1 u; treeb_member tree2 u; int_eq u x]
              );
      ])
in
let preds = ["treeb_member";] in
(* let total_env = SpecAbd.multi_infer
 *     (sprintf "%s%i" testname 1) ctx pre post elems spectable holel preds bpreds 1 in *)
let spectable = add_spec predefined_spec_tab "BalancePre"
    [T.Bool, "r1"; T.IntTreeB, "tree1"; T.Int, "x"; T.IntTreeB, "tree2";T.IntTreeB, "tree3"]
    [T.Int, "u"; T.Int, "v"]
    (E.And [
        E.Implies (treeb_any_order tree1 u v, Not (int_eq u v));
        E.Implies (treeb_any_order tree2 u v, Not (int_eq u v));
        E.Implies (E.And [treeb_member tree1 u; treeb_member tree1 v],
                   Not (int_eq u v));
        E.Implies (E.Or[treeb_member tree1 u; treeb_member tree2 u], Not (int_eq u x));
      ])
in
let spectable = add_spec spectable "BalancePost"
    [T.Bool, "r1"; T.IntTreeB, "tree1"; T.Int, "x"; T.IntTreeB, "tree2";T.IntTreeB, "tree3"]
    [T.Int, "u"; T.Int, "v"]
    (E.And [
        (* tree_once tree3 u; *)
        (* E.Implies(tree_member tree3 u, tree_once tree3 u); *)
        E.Implies (treeb_any_order tree3 u v, Not (int_eq u v));
        E.Iff (treeb_member tree3 u,
               E.Or [treeb_member tree1 u; treeb_member tree2 u; int_eq u x]
              );
      ])
in
let preds = ["treeb_member"; "treeb_left"; "treeb_right"; "treeb_parallel"] in
let total_env = SpecAbd.multi_infer
    (sprintf "%s%i" testname 2) ctx pre post elems spectable holel preds bpreds 2 in
();;
