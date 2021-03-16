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
let ctx = init () in
let preds = ["list_member"; "list_head"] in
let bpreds = ["=="] in
let trace1_value = [
  "is_empty", [V.B false;V.L [1;2];];
  "top", [V.L [1;2]; V.I 1];
  "tail", [V.L [1;2]; V.L [2]];
  "concat", [V.L [2]; V.L [2;3]; V.L [2;2;3]];
  "push", [V.I 1; V.L [2;2;3]; V.L [1;2;2;3]];] in
let trace2_value = [
  "is_empty", [ V.B true; V.L [];];] in
let concat, concat_hole = make_hole "concat" [T.IntList; T.IntList; T.IntList] in
let is_empty, is_empty_hole = make_hole "is_empty" [T.Bool;T.IntList;] in
let top, top_hole = make_hole "top" [T.IntList; T.Int] in
let tail, tail_hole = make_hole "tail" [T.IntList; T.IntList] in
let push, push_hole = make_hole "push" [T.Int; T.IntList; T.IntList] in
let spectable = predefined_spec_tab in
let s1, s2, nu_tail, nu_concat, nu_push, nu =
  map6 list_var ("s1", "s2", "nu_tail", "nu_concat", "nu_push", "nu") in
let nu_is_empty = bool_var "nu_is_empty" in
let nu_top = int_var "nu_top" in
let vc =
  Ast.Ite (is_empty [nu_is_empty; s1;],
           poly_eq [s2;nu],
           And [top [s1; nu_top];
                tail [s1; nu_tail];
                concat [nu_tail; s2; nu_concat];
                push [nu_top; nu_concat; nu;]
               ]
          )
in
let holes = [is_empty_hole; concat_hole; top_hole; push_hole; tail_hole] in
let vc, holes = instantiate_bool vc holes in
let _ = Printf.printf "vc:\n%s\n" (Ast.layout vc) in
let _ = List.iter (fun hole ->
    Printf.printf "?%s(%s)\n" hole.name (List.to_string T.layouttvar hole.args)
  ) holes
in
();;
