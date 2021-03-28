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
let e, e_hole = make_hole_from_info
    {name = "e"; intps = []; outtps = [T.IntTreeI];
     prog = function
       | [] -> Some [V.TI LabeledTree.Leaf]
       | _ -> raise @@ InterExn "bad prog"
    } in
let t, t_hole = make_hole_from_info
    {name = "t"; intps = [T.Int; T.Int; T.IntTreeI; T.IntTreeI]; outtps = [T.IntTreeI];
     prog = function
       | [V.I r; V.I x; V.TI a; V.TI b] -> Some [V.TI (LabeledTree.Node(r,x,a,b))]
       | _ -> raise @@ InterExn "bad prog"
    } in
let maket, maket_hole = make_hole_from_info
    {name = "maket"; intps = [T.Int; T.IntTreeI; T.IntTreeI]; outtps = [T.IntTreeI];
     prog = function
       | [V.I x; V.TI a; V.TI b] ->
         let result =
           LabeledTree.(
             let rank = function Leaf -> 0 | Node (r, _, _ ,_) -> r in
             if rank a >= rank b
             then Node (rank b + 1, x, a, b)
             else Node (rank a + 1, x, b, a)
           )
         in
         Some [V.TI result]
       | _ -> raise @@ InterExn "bad prog"
    } in
let merge args =
  Implies (SpecApply ("MergePre", args), SpecApply ("MergePost", args)) in
let pre =
  Ast.make_match [T.IntTreeI, "tree1"; T.IntTreeI, "tree2";]
    [T.IntTreeI, "tree3"]
    [(Some (And [e [te;];]),
      [T.IntTreeI, "tree1"; T.IntTreeI, "te";]),
     (None,
      [(T.IntTree, "tree1");]);
     (Some (And [e [te;];]),
      [T.IntTreeI, "te"; T.IntTreeI, "tree2";]),
     (None,
      [(T.IntTree, "tree2");]);
     (Some (And [t [rank1;x;a1;b1;tree1]; t [rank2;y;a2;b2;tree2]]),
      [T.IntTreeI, "tree1"; T.IntTreeI, "tree2";]),
     (Some(
         Ite(le [x;y;nu_le;],
             And[
               merge [b1;tree2;tmp1]; maket [x;a2;tmp1;nu]],
             And[
               merge [tree1;b2;tmp1]; maket [y;a2;tmp1;nu]])
       ),
      [(T.IntTreeI, "nu");]);
    ]
in
let post = merge [tree1;tree2;tree3] in
let elems = [T.Int, "x"; T.Int, "y"] in
(* let vc =
 *   Ast.Ite(e [nu_e2; tree2;],
 *           merge [tree1; tree2; tree1],
 *           Ite(e [nu_e1; tree1],
 *               merge [tree1; tree2; tree2],
 *               Implies (And [t [rank1;x;a1;b1;tree1]; t [rank2;y;a2;b2;tree2]],
 *                        Ite(le [nu_le;x;y],
 *                            Implies(And[
 *                                merge [b1;tree2;tmp1]; makeT [x;a2;tmp1;nu]],
 *                                    merge [tree1; tree2; nu]
 *                              ),
 *                            Implies(And[
 *                                merge [tree1;b2;tmp1]; makeT [y;a2;tmp1;nu]],
 *                                    merge [tree1; tree2; nu]
 *                              ))
 *                           )
 *                       )
 *          )
 *     in *)
let holel = [e_hole;
             t_hole;
             maket_hole
            ] in
let spectable = add_spec predefined_spec_tab "MergePre"
    [T.IntTreeI, "tree1";T.IntTreeI, "tree2";T.IntTreeI, "tree3"]
    []
    (E.True) in
let spectable = add_spec spectable "MergePost"
    [T.IntTreeI, "tree1";T.IntTreeI, "tree2";T.IntTreeI, "tree3"]
    [T.Int, "u"]
    (E.And [
        (E.Iff (treei_member tree3 u, E.Or [treei_member tree1 u; treei_member tree2 u]));
      ])

in
let total_env = SpecAbd.multi_infer
    (sprintf "%s%i" testname 1) ctx pre post elems spectable holel preds bpreds 1 in
let spectable = add_spec spectable "MergePost"
    [T.IntTreeI, "tree1";T.IntTreeI, "tree2";T.IntTreeI, "tree3"]
    [T.Int, "u"]
    (E.And [
        E.Implies (treei_head tree3 u,
                   E.Or [treei_head tree1 u; treei_head tree2 u;]);
        (E.Iff (treei_member tree3 u, E.Or [treei_member tree1 u; treei_member tree2 u]));
      ])

in
let total_env = SpecAbd.multi_infer
    (sprintf "%s%i" testname 2) ctx pre post elems spectable holel preds bpreds 1 in
();;
