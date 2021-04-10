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
let bench_name = "leftisthp" in
let ctx = init () in
let tree0 = treei_var "tree0" in
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
     (Some (And [t [rank1;x;a1;b1;tree1]; t [rank1;y;a2;b2;tree2]]),
      [T.IntTreeI, "tree1"; T.IntTreeI, "tree2";]),
     (Some(
         Ite(le [x;y;nu_le;],
             And[
               merge [b1;tree2;tmp1]; maket [x;a1;tmp1;tree3]],
             And[
               merge [tree1;b2;tmp1]; maket [y;a2;tmp1;tree3]])
       ),
      [(T.IntTreeI, "tree3");]);
    ]
in
let client_code tree1 tree2 =
  let open LabeledTree in
  let rank = function Leaf -> 0 | Node (r,_,_,_) -> r in
  let makeT x a b =
    if rank a >= rank b then Node (rank b + 1, x, a, b)
    else Node (rank a + 1, x, b, a)
  in
  let rec merge tree1 tree2 =
    match tree1, tree2 with
    | tree1, Leaf -> tree1
    | Leaf, tree2 -> tree2
    | Node (rank1, x, a1, b1), Node (rank2, y, a2, b2) ->
      if x <= y then makeT x a1 (merge b1 tree2)
      else makeT y a2 (merge tree1 b2)
  in
  merge tree1 tree2
in
let mii =
  let open SpecAbd in
  {upost = merge [tree1;tree2;tree3];
   uvars = [T.Int, "x"; T.Int, "y"];
   uinputs = [T.IntTreeI, "tree1"; T.IntTreeI, "tree2";];
   uoutputs = [T.IntTreeI, "tree3";];
   uprog = function
     | [V.TI tree1; V.TI tree2] -> Some [V.TI (client_code tree1 tree2)]
     | _ -> raise @@ InterExn "bad prog"
  }
in
let holel = [e_hole;
             maket_hole;
             t_hole;
            ] in
let which_bench = Array.get Sys.argv 1 in
let if_diff = try Some (Array.get Sys.argv 2) with _ -> None in
if String.equal which_bench "1" then
  let preds = ["treei_member";] in
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
  match if_diff with
  | Some _ ->
    let _ = SpecAbd.find_weakened_model
        (sprintf "%s%s" bench_name which_bench) ctx mii pre spectable in
    ()
  | None ->
    let total_env = SpecAbd.multi_infer
        (sprintf "%s%s" bench_name which_bench) ctx mii pre spectable holel preds 1 in
    ()
else if String.equal which_bench "2" then
  let spectable = add_spec predefined_spec_tab "MergePre"
      [T.IntTreeI, "tree1";T.IntTreeI, "tree2";T.IntTreeI, "tree3"]
      [T.Int, "u"; T.Int, "v"]
      (And [
          Implies (treei_ancestor tree1 u v, int_le u v);
          Implies (treei_ancestor tree2 u v, int_le u v);
        ]) in
  let spectable = add_spec spectable "MergePost"
      [T.IntTreeI, "tree1";T.IntTreeI, "tree2";T.IntTreeI, "tree3"]
      [T.Int, "u"; T.Int, "v"]
      (E.And [
          Implies (treei_ancestor tree3 u v, int_le u v);
          (E.Iff (treei_member tree3 u, E.Or [treei_member tree1 u; treei_member tree2 u]));
        ])
  in
  let preds = ["treei_member";"treei_ancestor"] in
  match if_diff with
  | Some _ ->
    let _ = SpecAbd.find_weakened_model
        (sprintf "%s%s" bench_name which_bench) ctx mii pre spectable in
    ()
  | None ->
    let total_env = SpecAbd.multi_infer
        (sprintf "%s%s" bench_name which_bench) ctx mii pre spectable holel preds 1 in
    ()
else raise @@ InterExn "no such bench";;

(* let spectable = set_spec spectable "t"
 *     [T.Int, "rank"; T.Int, "x"; T.IntTree, "tree0"; T.IntTree, "tree1";T.IntTree, "tree2"]
 *     [T.Int, "u";T.Int, "v";]
 *     (And [
 *         Iff (treei_head tree2 u, int_eq x u);
 *         Iff (treei_member tree2 u,
 *              Or [treei_member tree0 u; treei_member tree1 u; int_eq x u]);
 *         Iff (treeil tree2 u v, Or [
 *             treeil tree0  u v;
 *             treeil tree1 u v;
 *             And [int_eq x u; treei_member tree0 v];
 *           ]);
 *         Iff (treeir tree2 u v, Or [
 *             treeir tree0  u v;
 *             treeir tree1 u v;
 *             And [int_eq x u; treei_member tree1 v];
 *           ]);
 *         (\* Implies (And [int_eq x u; treei_member tree0 v], treeil tree2 u v);
 *          * Implies (And [int_eq x u; treei_member tree1 v], treeir tree2 u v); *\)
 *       ])
 * in
 * let spectable = set_spec spectable "maket"
 *     [T.Int, "x"; T.IntTree, "tree0"; T.IntTree, "tree1";T.IntTree, "tree2"]
 *     [T.Int, "u";T.Int, "v";]
 *     (And [
 *         Iff (treei_head tree2 u, int_eq x u);
 *         Iff (treei_member tree2 u,
 *              Or [treei_member tree0 u; treei_member tree1 u; int_eq x u]);
 *         Iff (treeil tree2 u v, Or [
 *             treeil tree0  u v;
 *             treeil tree1 u v;
 *             And [int_eq x u; treei_member tree0 v];
 *           ]);
 *         Iff (treeir tree2 u v, Or [
 *             treeir tree0  u v;
 *             treeir tree1 u v;
 *             And [int_eq x u; treei_member tree1 v];
 *           ]);
 *       ])
 * in *)
