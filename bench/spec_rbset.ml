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
let bench_name = "rbset" in
let ctx = init () in
let tree0 = treeb_var "tree0" in
let tree1, tree2, tree3, a, b, c, d =
  map7 treeb_var ("tree1", "tree2", "tree3", "a", "b", "c", "d") in
let te, nu, tmp1, tmp2, tmp3, tmp4 = map6 treeb_var
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
      (Some (And [black [r1]; red [r2];
                  t [r2;a;x;b;tmp1];t [r2;tmp1;y;c;tree1];]),
       [T.Bool, "r1"; T.IntTreeB, "tree1"; T.Int, "z"; T.IntTreeB, "d";]),
      (Some (And [t [r1;a;x;b;tmp2]; t [r1;c;z;d;tmp3]; t[r2;tmp2;y;tmp3;tmp4];]),
       [(T.IntTree, "tmp4");]);
      (Some (And [black [r1]; red [r2];
                  t [r2;b;y;c;tmp1]; t[r2;a;x;tmp1;tree1];]),
       [T.Bool, "r1"; T.IntTreeB, "tree1"; T.Int, "z"; T.IntTreeB, "d";]),
      (Some (And [t [r1;a;x;b;tmp2]; t [r1;c;z;d;tmp3]; t [r2;tmp2;y;tmp3;tmp4];]),
       [(T.IntTree, "tmp4");]);
      (Some (And [black [r1]; red [r2];
                  t [r2;b;y;c;tmp1];t [r2;tmp1;z;d;tree2];]),
       [T.Bool, "r1"; T.IntTreeB, "a"; T.Int, "x"; T.IntTreeB, "tree2";]),
      (Some (And [t [r1;a;x;b;tmp2]; t [r1;c;z;d;tmp3]; t[r2;tmp2;y;tmp3;tmp4];]),
       [(T.IntTree, "tmp4");]);
      (Some (And [black [r1]; red [r2];
                  t [r2;c;z;d;tmp1];t [r2;b;y;tmp1;tree2];]),
       [T.Bool, "r1"; T.IntTreeB, "a"; T.Int, "x"; T.IntTreeB, "tree2";]),
      (Some (And [t [r1;a;x;b;tmp2]; t [r1;c;z;d;tmp3]; t[r2;tmp2;y;tmp3;tmp4];]),
       [(T.IntTree, "tmp4");]);
      (* (Some (And [black [r1]; red [r2]; e [te;];
       *             t [r2;te;x;te;tree1];]),
       *  [T.Bool, "r1"; T.IntTreeB, "tree1"; T.Int, "z"; T.IntTreeB, "d";]),
       * (Some (And [t [r2;tree1;z;d;tmp4];]),
       *  [(T.IntTree, "tmp4");]); *)
      (* (Some (And [black [r1]; red [r2]; e [te;];
       *             t [r2;b;y;c;tmp1]; t [r2;tmp1;z;d;tree2];]),
       *  [T.Bool, "r1"; T.IntTreeB, "te"; T.Int, "x"; T.IntTreeB, "tree2";]),
       * (Some (And [t [r1;te;x;b;tmp2]; t [r1;c;z;d;tmp3]; t[r2;tmp2;y;tmp3;tmp4];]),
       *  [(T.IntTree, "tmp4");]); *)
      (* (Some (And [black [r1]; red [r2]; e [te;];
       *             t [r2;c;z;d;tmp1]; t [r2;te;y;tmp1;tree2];]),
       *  [T.Bool, "r1"; T.IntTreeB, "te"; T.Int, "x"; T.IntTreeB, "tree2";]),
       * (Some (And [t [r1;te;x;te;tmp2]; t [r1;c;z;d;tmp3]; t [r2;tmp2;y;tmp3;tmp4];]),
       *  [(T.IntTree, "tmp4");]);
       * (Some (And [black [r1]; red [r2]; e [te;];
       *             ]),
       *  [T.Bool, "r1"; T.IntTreeB, "te"; T.Int, "x"; T.IntTreeB, "te";]),
       * (Some (t [r2;te;x;te;tmp4];),
       *  [(T.IntTree, "tmp4");]); *)
      (Some (And [black [r1]; red [r2];
                 ]),
       [T.Bool, "r"; T.IntTreeB, "tree1"; T.Int, "x"; T.IntTreeB, "tree2";]),
      (Some (t [r;tree1;x;tree2;tmp4];),
       [(T.IntTree, "tmp4");]);
    ]
in
let client_code r tree1 x tree2 =
  let open LabeledTree in
  let balance = function
    | false, Node (true, y, Node (true, x, a, b), c), z, d
    | false, Node (true, x, a, Node (true, y, b, c)), z, d
    | false, a, x, Node (true, z, Node (true, y, b, c), d)
    | false, a, x, Node (true, y, b, Node (true, z, c, d)) ->
      Node (true, y, Node (false, x, a, b), Node (false, z, c, d))
    | a, b, c, d -> Node (a, c, b, d)
  in
  balance (r, tree1, x, tree2)
in
let mii =
  let open SpecAbd in
  {upost =  balance [r;tree1;x;tree2;tree3];
   uvars = [T.Int, "x"; T.Int, "y"];
   uinputs = [T.Bool, "r"; T.IntTreeB, "tree1"; T.Int, "x"; T.IntTreeB, "tree2";];
   uoutputs = [T.IntTreeB, "tree3";];
   uprog = function
     | [V.B r; V.TB tree1; V.I x; V.TB tree2] ->
       Some [V.TB (client_code r tree1 x tree2)]
     | _ -> raise @@ InterExn "bad prog"
  }
in
let holel = [
  (* e_hole; *)
  t_hole
] in
let which_bench = Array.get Sys.argv 1 in
if String.equal which_bench "1" then
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
  let total_env = SpecAbd.multi_infer
      (sprintf "%s%s" bench_name which_bench) ctx mii pre spectable holel preds 1 in
  ()
else if String.equal which_bench "2" then
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
      (sprintf "%s%s" bench_name which_bench) ctx mii pre spectable holel preds 1 in
  ()
else raise @@ InterExn "no such bench"
;;
(* let spectable = set_spec spectable "t"
 *     [T.Bool, "rb"; T.IntTree, "tree0"; T.Int, "x"; T.IntTree, "tree1";T.IntTree, "tree2"]
 *     [T.Int, "u";T.Int, "v";]
 *     (And [
 *         (\* Iff (treeb_head tree2 u, int_eq x u); *\)
 *         Iff (treeb_member tree2 u,
 *              Or [treeb_member tree0 u; treeb_member tree1 u; int_eq x u]);
 *         Iff (treebl tree2 u v, Or [
 *             treebl tree0  u v;
 *             treebl tree1 u v;
 *             And [int_eq x u; treeb_member tree0 v];
 *           ]);
 *         Iff (treebr tree2 u v, Or [
 *             treebr tree0  u v;
 *             treebr tree1 u v;
 *             And [int_eq x u; treeb_member tree1 v];
 *           ]);
 *         Iff (treebp tree2 u v, Or [
 *             treebp tree0  u v;
 *             treebp tree1 u v;
 *             And [treeb_member tree0 u; treeb_member tree1 v];
 *           ]);
 *         (\* Implies (And [int_eq x u; treeb_member tree0 v], treebl tree2 u v);
 *          * Implies (And [int_eq x u; treeb_member tree1 v], treebr tree2 u v); *\)
 *       ])
 * in *)
