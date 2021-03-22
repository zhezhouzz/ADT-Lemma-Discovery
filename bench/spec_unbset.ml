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
let preds = ["tree_member";] in
let bpreds = ["=="] in
let tree1, tree2, tree3, a1, a2, b1, b2 =
  map7 treei_var ("tree1", "tree2", "tree3", "a1", "a2", "b1", "b2") in
let nu_e, nu_t, nu, nu_insert = map4 tree_var ("nu_e", "nu_t", "nu", "nu_insert") in
let x, y, rank1, rank2 = map4 int_var ("x", "y", "rank1", "rank2") in
let nu_lt1, nu_lt2 = map_double bool_var ("nu_lt1", "nu_lt2") in
let e_program = function
  | [] -> Some [V.T Tree.Leaf]
  | _ -> raise @@ InterExn "bad prog"
in
let t_program = function
  | [V.T left; V.I x; V.T right] -> Some [V.T (Tree.Node (x, left, right))]
  | _ -> raise @@ InterExn "bad prog"
in
let e, e_hole =
  make_hole "e" [T.IntTree;] e_program in
let t, t_hole =
  make_hole "t" [T.IntTree;T.Int;T.IntTree;T.IntTree] t_program in
let insert args = SpecApply ("Insert", args) in
let pre =
  Ast.make_match [T.IntTree, "tree3"]
    [
      ([e [nu_e], (T.IntTree, "nu_e")], t [nu_e;x;nu_e;nu]);
      ([t [tree1; y; tree2; nu_t], (T.IntTree, "nu_t")],
       Ite(lt [x;y;nu_lt1;],
           And [insert [x;tree1;nu_insert];
                t [nu_insert;y;tree2;nu]],
           Ite(lt [y;x;nu_lt2;],
               And [insert [x;tree2;nu_insert];
                    t [tree1;y;nu_insert;nu]],
               t [tree1;y;tree2;nu]
              )
          )
      );
    ] in
let post = insert [x; tree3; nu] in
let holel = [e_hole;t_hole] in
let spectable = predefined_spec_tab in
(* let spectable = set_spec spectable "Insert"
 *     [T.Int, "x";T.IntTree, "tree1";T.IntTree, "tree2"] [T.Int, "u"]
 *     (E.And [
 *         E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
 *       ])
 * in
 * let total_env = SpecAbd.multi_infer ctx pre post spectable holel preds bpreds 1 1 in *)
let preds = ["tree_member";"tree_head"] in
let spectable = set_spec spectable "Insert"
    [T.Int, "x";T.IntTree, "tree1";T.IntTree, "tree2"] [T.Int, "u"]
    (E.And [
        E.Implies(And [tree_head tree1 u; int_lt u x], tree_head tree2 u);
        E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
      ])
in
let total_env = SpecAbd.multi_infer ctx pre post spectable holel preds bpreds 1 1 in
(* let spectable = set_spec spectable "Insert"
 *     [T.Int, "x";T.IntTree, "tree1";T.IntTree, "tree2"] [T.Int, "u"]
 *     (E.And [
 *         E.Implies(tree_head tree1 x,
 *                   E.Implies (treel tree1 u v, treel tree2 u v)
 *                  );
 *         E.Iff (tree_member tree2 u, E.Or [tree_member tree1 u; int_eq u x]);
 *       ])
 * in *)
();;
