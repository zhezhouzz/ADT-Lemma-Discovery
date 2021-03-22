module Ast = Language.SpecAst
module Value = Pred.Value
module SpecAbd = Inference.SpecAbduction;;
module Env = Inference.Env;;

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
let concat_program = function
  | [V.L l1; V.L l2] -> Some [V.L (l1 @ l2)]
  | _ -> raise @@ InterExn "bad prog"
in
let concat, concat_hole =
  make_hole "concat" [T.IntList; T.IntList; T.IntList] concat_program in
let is_empty_program = function
  | [V.L []] -> Some [V.B true]
  | [V.L _] -> Some [V.B false]
  | _ -> raise @@ InterExn "bad prog"
in
let is_empty, is_empty_hole = make_hole "is_empty" [T.Bool;T.IntList;] is_empty_program in
let top_program = function
  | [V.L []] -> None
  | [V.L (h :: _)] -> Some [V.I h]
  | _ -> raise @@ InterExn "bad prog"
in
let top, top_hole = make_hole "top" [T.IntList; T.Int] top_program in
let tail_program = function
  | [V.L []] -> None
  | [V.L (_ :: t)] -> Some [V.L t]
  | _ -> raise @@ InterExn "bad prog"
in
let tail, tail_hole = make_hole "tail" [T.IntList; T.IntList] tail_program in
let push_program = function
  | [V.I x; V.L l] -> Some [V.L (x :: l)]
  | _ -> raise @@ InterExn "bad prog"
in
let push, push_hole = make_hole "push" [T.Int; T.IntList; T.IntList] push_program in
let spectable = predefined_spec_tab in
let spectable = set_post spectable
    [T.IntList, "l1";T.IntList, "l2";T.IntList, "l3"]
    [T.Int, "u"]
    (E.And [
        E.Iff (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
        E.Implies (list_head l3 u, E.Or [list_head l1 u; list_head l2 u]);
      ])
in
let s1, s2, nu_tail, nu_concat, nu_push, nu =
  map6 list_var ("s1", "s2", "nu_tail", "nu_concat", "nu_push", "nu") in
let nu_is_empty = bool_var "nu_is_empty" in
let nu_top = int_var "nu_top" in
let pre =
  Ast.Ite (is_empty [nu_is_empty; s1;],
           poly_eq [s2;nu],
           And [top [s1; nu_top];
                tail [s1; nu_tail];
                concat [nu_tail; s2; nu_concat];
                push [nu_top; nu_concat; nu;]
               ]
          )
in
let post = bench_post [s1;s2;nu] in
(* let _ = SpecAbd.sampling concat_hole () 10 in *)
let holel = [is_empty_hole;
             concat_hole;
             top_hole;
             push_hole;
             tail_hole] in
(* let _ = Printf.printf "vc:\n%s\n" (Ast.layout vc) in
 * let _ = List.iter (fun hole ->
 *     Printf.printf "?%s(%s)\n" hole.name (List.to_string T.layouttvar hole.args)
 *   ) holes *)
(* in *)
let total_env = SpecAbd.multi_infer ctx pre post spectable holel preds bpreds 1 1 in
(* let _ = StrMap.iter (fun name spec ->
 *     printf "%s\n" (Ast.layout_spec_entry name spec)
 *   ) (total_env.spectable) in
 * let _ = printf "finished\n" in *)
();;
