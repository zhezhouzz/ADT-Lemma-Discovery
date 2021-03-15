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
let spectable = predefined_spec_tab in
let _, concat = add_spec_ret_fun spectable "StackConcat" ["l1";"l2";"l3"] ["u"]
    (E.And [
        E.Implies (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
        E.Implies (list_head l3 u, E.Or [list_head l1 u; list_head l2 u])
      ])
in
let spectable, post = add_spec_ret_fun spectable "Post" ["l1";"l2";"l3";"l4"] ["u"]
    (E.And [
        E.Iff (list_member l4 u, E.Or [list_member l1 u; list_member l2 u; list_member l3 u]);
        E.Implies (list_head l4 u, E.Or [list_head l1 u; list_head l2 u; list_head l3 u]);
      ])
in
let s1, s2, s3, nu_concat, nu = map5 list_var ("s1", "s2", "s3", "nu_concat", "nu") in
let nu_top = int_var "nu_top" in
let vc =
  Implies (And [concat [s1; s2; nu_concat];
                concat [nu_concat; s3; nu];],
           post [s1; s2; s3; nu])
in
let preds = ["list_member"; "list_head"] in
let bpreds = ["=="] in
let concat_hole = {SpecAbd.name = "StackConcat";
                   SpecAbd.funtype =
                     [T.IntList, "l1";T.IntList, "l2"; T.IntList, "l3"];
                   SpecAbd.inout = [
                     [V.L [2]; V.L [2;3];  V.L [2;2;3];];
                     [V.L [1;2]; V.L [2;3];  V.L [1;2;2;3];];
                     [V.L [2]; V.L [1;2];  V.L [2;1;2];];
                     [V.L [2;3]; V.L [];  V.L [2;3];];
                     [V.L []; V.L [2;3];  V.L [2;3];];
                     [V.L [2]; V.L [];  V.L [2];];
                     [V.L [2;3]; V.L [1;3];  V.L [2;3;1;3];];
                     [V.L [1;1]; V.L [1;1];  V.L [1;1;1;1];];
                   ]} in
let make_data k v =
  List.fold_left (fun m (k, v) ->
      StrMap.add k v m
    ) (StrMap.empty) (List.combine k v) in
let lemma = ["s1"; "s2"; "u"], (
    E.And [])in
let holes = [concat_hole;] in
let result = SpecAbd.multi_infer ctx vc spectable holes preds bpreds 1 1 lemma in
let _ = match result with
  | None -> Printf.printf "no result\n"
  | Some result ->
    let _ = List.map (fun (name, args, spec) ->
        Printf.printf "%s(%s):\n\t%s\n" name
          (List.to_string snd args)
          (E.pretty_layout_forallformula spec)
      ) result in ()
in
();;
