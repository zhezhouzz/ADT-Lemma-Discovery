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
let bench_name = "unbset" in
let ctx = init () in
let bpreds = ["=="] in
let tree0 = tree_var "tree0" in
let tree1, tree2, tree3, a1, a2, b1, b2 =
  map7 treei_var ("tree1", "tree2", "tree3", "a1", "a2", "b1", "b2") in
let nu_e, nu_t, nu, nu_insert = map4 tree_var ("nu_e", "nu_t", "nu", "nu_insert") in
let x, y = map_double int_var ("x", "y") in
let nu_lt1, nu_lt2 = map_double bool_var ("nu_lt1", "nu_lt2") in
let e, e_hole = make_hole_from_info
    {name = "e"; intps = []; outtps = [T.IntTree;];
     prog = function
       | [] -> Some [V.T Tree.Leaf]
       | _ -> raise @@ InterExn "bad prog"} in
let t, t_hole = make_hole_from_info
    {name = "t"; intps = [T.IntTree;T.Int;T.IntTree;]; outtps = [T.IntTree;];
     prog = function
       | [V.T left; V.I x; V.T right] -> Some [V.T (Tree.Node (x, left, right))]
       | _ -> raise @@ InterExn "bad prog"} in
let insert args = SpecApply ("Insert", args) in
let pre =
  Ast.make_match [T.IntTree, "tree3"] [T.IntTree, "nu"]
    [
      (Some (e [nu_e]), [(T.IntTree, "nu_e")]), (Some (t [nu_e;x;nu_e;nu]), [(T.IntTree, "nu")]);
      (Some (t [tree1; y; tree2; nu_t]), [(T.IntTree, "nu_t")]),
      (Some (
          Ite(lt [x;y;nu_lt1;],
              And [insert [x;tree1;nu_insert];
                   t [nu_insert;y;tree2;nu]],
              Ite(lt [y;x;nu_lt2;],
                  And [insert [x;tree2;nu_insert];
                       t [tree1;y;nu_insert;nu]],
                  t [tree1;y;tree2;nu]
                 )
             )),
       [(T.IntTree, "nu")]
      );
    ] in
let post = insert [x; tree3; nu] in
let elems = [T.Int, "x"; T.Int, "y";] in
let holel = [e_hole;
             t_hole
            ] in
let preds = ["tree_member";] in
let spectable = set_spec predefined_spec_tab "Insert"
    [T.Int, "x";T.IntTree, "tree1";T.IntTree, "tree2"] [T.Int, "u"]
    (E.And [
        E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
      ])
in
(* let total_env = SpecAbd.multi_infer
 *     (sprintf "%s%i" bench_name 1) ctx pre post elems spectable holel preds bpreds 1 in *)
let preds = ["tree_member";"tree_head"] in
let spectable = set_spec predefined_spec_tab "Insert"
    [T.Int, "x";T.IntTree, "tree1";T.IntTree, "tree2"] [T.Int, "u"]
    (E.And [
        E.Implies(And [tree_head tree1 u; int_lt u x], tree_head tree2 u);
        E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
      ])
in
(* let total_env = SpecAbd.multi_infer
 *     (sprintf "%s%i" bench_name 2) ctx pre post elems spectable holel preds bpreds 1 in *)
let spectable = set_spec predefined_spec_tab "Insert"
    [T.Int, "x";T.IntTree, "tree1";T.IntTree, "tree2"] [T.Int, "u"]
    (E.And [
        E.Implies(tree_head tree1 u,
                  And [
                    (* E.Implies (treel tree1 u v, treel tree2 u v) *)
                    E.Implies(int_lt x u, treel tree2 u x);
                    (* E.Implies(int_gt x u, treer tree2 u x); *)
                  ]);
        E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
      ])
in
(* let spectable = set_spec spectable "t"
 *     [T.IntTree, "tree0";T.Int, "x";T.IntTree, "tree1";T.IntTree, "tree2"]
 *     [T.Int, "u";T.Int, "v";]
 *     (And [
 *         Iff (tree_head tree2 u, int_eq x u);
 *         Iff (tree_member tree2 u, Or [tree_member tree0 u; tree_member tree1 u; int_eq x u]);
 *         Iff (treel tree2 u v, Or [
 *             treel tree0  u v;
 *             treel tree1 u v;
 *             And [int_eq x u; tree_member tree0 v];
 *           ]);
 *         (\* Iff (treer tree2 u v, Or [
 *          *     treer tree0 u v;
 *          *     treer tree1 u v;
 *          *     And [int_eq x u; tree_member tree1 v];
 *          *   ]); *\)
 *       ])
 * in *)
let preds = ["tree_member";"tree_head";"tree_left"] in
let total_env = SpecAbd.multi_infer
    (sprintf "%s%i" bench_name 3) ctx pre post elems spectable holel preds bpreds 2 in
();;
