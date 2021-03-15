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
let argl1 = T.IntList, "l1" in
let argl2 = T.IntList, "l2" in
let argnu_l = T.IntList, "nu_l" in
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
           bench_post [s1; s2; s2],
           Implies (And [top [s1; nu_top];
                         tail [s1; nu_tail];
                         concat [nu_tail; s2; nu_concat];
                         push [nu_top; nu_concat; nu;]],
                    bench_post [s1; s2; nu])
          )
in
let vcs = Ast.eliminate_cond vc in
let holes = [is_empty_hole; concat_hole; top_hole; push_hole; tail_hole] in
let traces = [trace1_value; trace2_value] in
let spectable = set_post spectable ["l1";"l2";"l3"] ["u"]
    (E.And [
        E.Iff (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
        E.Implies (list_head l3 u, E.Or [list_head l1 u; list_head l2 u]);
      ])
in
let result = SpecAbd.multi_infer ctx vcs spectable holes preds bpreds 1 1 traces in
let _ = match result with
  | None -> Printf.printf "no result\n"
  | Some (spectable, _) ->
    let spectable = StrMap.remove "top" spectable in
    let _ = StrMap.iter (fun name spec ->
        printf "[Max]:%s\n" (Ast.layout_spec_entry name spec)
      ) spectable in
    let test_m_env = {
      SpecAbd.spectable = spectable;
      SpecAbd.phi =
      [T.IntList, "s1"; T.IntList, "s2"; T.IntList, "nu_tail"; T.IntList, "nu_concat";
       T.IntList, "nu_push"; T.IntList, "nu";
       T.Int, "nu_top"],
      Ast.Implies (And [tail [s1; nu_tail];
                        concat [nu_tail; s2; nu_concat];
                        push [nu_top; nu_concat; nu;]],
                   bench_post [s1; s2; nu]);
      SpecAbd.hole =
        [T.IntList, "s1"; T.Int, "nu_top"],
        top [s1; nu_top];
      SpecAbd.qv = ["u"];
    } in
    let _ = SpecAbd.maximal_abduction ctx test_m_env in
    ()
in
let _ = raise @@ InterExn "end" in
(* let _ = match result with
 *   | None -> Printf.printf "no result\n"
 *   | Some (spectable, result) ->
 *     let refined_hole = List.first result in
 *     let candidate = SpecAbd.max_spec ctx vcs spectable refined_hole in
 *     let candidate = match candidate with
 *       | None -> raise @@ InterExn "maxed"
 *       | Some candidate -> candidate
 *     in
 *     let refined_hole = SpecAbd.block candidate refined_hole in
 *     let candidate = SpecAbd.max_spec ctx vcs spectable refined_hole in
 *     let candidate = match candidate with
 *       | None -> raise @@ InterExn "maxed"
 *       | Some candidate -> candidate
 *     in
 *     let refined_hole = SpecAbd.reset_cache candidate refined_hole in
 *     let result = SpecAbd.refinement_loop ctx vcs spectable [refined_hole] preds bpreds in
 *     let _ = StrMap.iter (fun name spec ->
 *         printf "%s\n" (Ast.layout_spec_entry name spec)
 *       ) spectable in
 *     ()
 * in *)
let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
(* let spectable = set_post spectable ["l1";"l2";"l3"] ["u"]
 *     (E.And [
 *         E.Iff (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
 *       ])
 * in
 * let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in
 * let spectable = set_post spectable ["l1";"l2";"l3"] ["u"]
 *     (E.And [
 *         E.Implies(E.And[list_head l1 u], list_member l3 u);
 *       ])
 * in
 * let _ = test ctx vcs spectable holes preds bpreds 1 1 traces in *)
();;
