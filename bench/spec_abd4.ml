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
let _, is_empty = add_spec_ret_fun spectable "IsEmpty" ["l1"] ["u"]
    (E.And [E.Not (list_member l1 u);
            (* E.Implies(list_head l1 u, list_member l1 u) (\* lemma *\) *)
           ])
in
let _, stack_top = add_spec_ret_fun spectable "StackTop" ["l1"; "x"] ["u"]
    (E.And [
        E.Iff (list_head l1 u, int_eq u x);
        list_member l1 x (* lemma *)
      ])
in
let _, stack_tail = add_spec_ret_fun spectable "StackTail" ["l1"; "l2"] ["u"]
    (E.And [
        E.Implies(list_member l2 u, list_member l1 u);
        E.Implies(E.And [list_member l1 u; E.Not (list_head l1 u)], list_member l2 u);
        (* E.Implies(list_head l2 u, list_member l2 u); (\* lemma *\) *)
      ])
in
let _, stack_push = add_spec_ret_fun spectable "StackPush" ["x"; "l1"; "l2"] ["u"]
    (E.And [
        E.Iff(list_member l2 u, E.Or [list_member l1 u; int_eq u x]);
        E.Iff (list_head l2 u, int_eq u x);
        E.Implies(list_head l2 u, list_member l2 u); (* lemma *)
      ])
in
let _, concat = add_spec_ret_fun spectable "StackConcat" ["l1";"l2";"l3"] ["u"]
    (E.And [
        E.Implies (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
        E.Implies (list_head l3 u, E.Or [list_head l1 u; list_head l2 u])
      ])
in
let spectable, post = add_spec_ret_fun spectable "Post" ["l1";"l2";"l3"] ["u"]
    (E.And [
        E.Iff (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
        E.Implies (list_head l3 u, E.Or [list_head l1 u; list_head l2 u]);
      ])
in
let s1, s2, nu_tail, nu_concat, nu_push, nu =
  map6 list_var ("s1", "s2", "nu_tail", "nu_concat", "nu_push", "nu") in
let nu_top = int_var "nu_top" in
let vc =
  Ast.Ite (is_empty [s1],
           post [s1; s2; s2],
           Implies (And [stack_top [s1; nu_top];
                         stack_tail [s1; nu_tail];
                         concat [nu_tail; s2; nu_concat];
                         stack_push [nu_top; nu_concat; nu;]],
                    post [s1; s2; nu])
          )
in
(* let vc = post [s1; s2; s2]
 * in *)
let preds = ["list_member"; "list_head"] in
let bpreds = ["=="] in
let names = ["nu_top"; "s1"; "s2"; "nu_tail"; "nu_concat"; "nu"] in
let make_data k v =
  List.fold_left (fun m (k, v) ->
      StrMap.add k v m
    ) (StrMap.empty) (List.combine k v) in
let values1 = [V.I 1; V.L [1;2]; V.L [2;3]; V.L [2]; V.L [2;2;3]; V.L [1;2;2;3];] in
let values2 = [V.I 1; V.L [1;2]; V.L [1;2]; V.L [2]; V.L [2;1;2]; V.L [1;2;1;2];] in
let values3 = [V.I 1; V.L [1;2;3]; V.L []; V.L [2;3]; V.L [2;3]; V.L [1;2;3];] in
let values4 = [V.I 1; V.L [1]; V.L [2;3]; V.L []; V.L [2;3]; V.L [1;2;3];] in
let values5 = [V.I 1; V.L [1;2]; V.L []; V.L [2]; V.L [2;]; V.L [1;2;];] in
let values6 = [V.I 1; V.L [1;2;3]; V.L [1;3]; V.L [2;3]; V.L [2;3;1;3]; V.L [1;2;3;1;3];] in
let values7 = [V.I 1; V.L [1;1;1]; V.L [1;1]; V.L [1;1]; V.L [1;1;1;1]; V.L [1;1;1;1;1];] in
let is_empty_hole = {SpecAbd.name = "IsEmpty";
                     SpecAbd.funtype =
                       [T.IntList, "l1"];
                     SpecAbd.inout = [
                       [V.L []]
                     ]} in
let concat_hole = {SpecAbd.name = "StackConcat";
                   SpecAbd.funtype =
                     [T.IntList, "nu_tail";T.IntList, "s2"; T.IntList, "nu_concat"];
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
let top_hole = {SpecAbd.name = "StackTop";
                SpecAbd.funtype =
                  [T.IntList, "l1";T.Int, "nu"];
                SpecAbd.inout = [
                  [V.L [1;2]; V.I 1;];
                  [V.L [1;1]; V.I 1;];
                ]} in
let tail_hole = {SpecAbd.name = "StackTail";
                SpecAbd.funtype =
                  [T.IntList, "l1";T.IntList, "l_nu"];
                SpecAbd.inout = [
                  [V.L [1;2]; V.L [2]];
                  [V.L [2;1]; V.L [1];];
                  [V.L [1;1]; V.L [1]];
                ]} in
let push_hole = {SpecAbd.name = "StackPush";
                 SpecAbd.funtype =
                   [T.Int, "x"; T.IntList, "l1";T.IntList, "l_nu"];
                 SpecAbd.inout = [
                   [V.I 1; V.L [1;2]; V.L [1;1;2]];
                   [V.I 3; V.L [1;2]; V.L [3;1;2]];
                   [V.I 2; V.L [1;2]; V.L [2;1;2]];
                   [V.I 1; V.L []; V.L [1]];
                 ]} in
let make_data k v =
  List.fold_left (fun m (k, v) ->
      StrMap.add k v m
    ) (StrMap.empty) (List.combine k v) in
let samples = List.map (fun values -> make_data names values)
    [values1; values2; values3; values4; values5; values6; values7] in
let lemma = ["s1"; "s2"; "u"], (
    E.And [
      (* E.Implies (list_head s1 u, list_member s1 u); *)
      (* E.Implies (list_head s2 u, list_member s2 u); *)
    ])in
let holes = [is_empty_hole; concat_hole; top_hole; push_hole; tail_hole] in
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
