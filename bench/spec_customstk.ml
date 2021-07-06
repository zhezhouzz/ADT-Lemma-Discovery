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
;;
let sourcefile = "/Users/zhezhou/workspace/research/ADT-Spec-Inference/data/bench_customstack.ml"
let assertionfile1 = "/Users/zhezhou/workspace/research/ADT-Spec-Inference/data/bench_customstack_assertion.ml"
let tool_name = "ocamlc"
let ppf = Format.err_formatter

let parse sourcefile =
  let structure = Pparse.parse_implementation ~tool_name Format.err_formatter sourcefile in
  (* let _ = Printast.structure 0 Format.std_formatter structure in *)
  structure
;;

let _ = Printf.printf "zz:%s\n" (Sys.getcwd ()) in
let source = parse sourcefile in
let assertion1 = parse assertionfile1 in
(* let _ = printf "vc:=\n%s\n" (Ast.layout vc) in *)
(* let _ = StrMap.iter (fun name spec -> printf "%s\n" (Ast.layout_spec_entry name spec)) spectab in *)
(* let _ = raise @@ InterExn "end" in *)
let bench_name = "customstk" in
let ctx = init () in
let concat_program = function
  | [V.L l1; V.L l2] -> Some [V.L (l1 @ l2)]
  | _ -> raise @@ InterExn "bad prog"
in
let concat, concat_hole =
  make_hole "concat" [T.IntList; T.IntList; T.IntList] concat_program in
let is_empty, is_empty_hole = make_hole_from_info
    {name = "Stack.is_empty"; intps = [T.IntList;T.Bool;]; outtps = [];
     prog = function
       | [V.L []] -> Some [V.B true]
       | [V.L _] -> Some [V.B false]
       | _ -> raise @@ InterExn "bad prog"} in
let top_program = function
  | [V.L []] -> None
  | [V.L (h :: _)] -> Some [V.I h]
  | _ -> raise @@ InterExn "bad prog"
in
let top, top_hole = make_hole "Stack.top" [T.IntList; T.Int] top_program in
let tail_program = function
  | [V.L []] -> None
  | [V.L (_ :: t)] -> Some [V.L t]
  | _ -> raise @@ InterExn "bad prog"
in
let tail, tail_hole = make_hole "Stack.tail" [T.IntList; T.IntList] tail_program in
let push_program = function
  | [V.I x; V.L l] -> Some [V.L (x :: l)]
  | _ -> raise @@ InterExn "bad prog"
in
let push, push_hole = make_hole "Stack.push" [T.Int; T.IntList; T.IntList] push_program in
let s1, s2, nu_tail, nu_concat, nu_push, nu =
  map6 list_var ("s1", "s2", "nu_tail", "nu_concat", "nu_push", "nu") in
let nu_is_empty = bool_var "nu_is_empty" in
let nu_top = int_var "nu_top" in
let pre =
  Ast.Ite (is_empty [s1;nu_is_empty;],
           poly_eq [s2;nu],
           And [top [s1; nu_top];
                tail [s1; nu_tail];
                concat [nu_tail; s2; nu_concat];
                push [nu_top; nu_concat; nu;]
               ]
          )
in
let _ = printf "old:=\n%s\n" (Ast.layout pre) in
(* let _ = printf "new:=\n%s\n" (Ast.layout vc) in *)
(* let _ = raise @@ InterExn "end" in *)
(* let pre = vc in *)
let mii =
  let open SpecAbd in
  {upost = SpecApply("concat", [s1;s2;nu]);
   uvars = [T.Int, "nu_top"];
   uinputs = [T.IntList, "s1"; T.IntList, "s2"];
   uoutputs = [T.IntList, "nu"];
   uprog = function
     | [V.L s1; V.L s2] -> Some [V.L (s1 @ s2)]
     | _ -> raise @@ InterExn "bad prog"
  }
in
let which_bench = Array.get Sys.argv 1 in
let if_diff = try Some (Array.get Sys.argv 2) with _ -> None in
if String.equal which_bench "1" then
  let holel = [
    push_hole;
    is_empty_hole;
    top_hole;
    tail_hole] in
  let spectable_post = set_spec (predefined_spec_tab) "concat"
      [T.IntList, "l1";T.IntList, "l2";T.IntList, "l3"]
      [T.Int, "u"]
      (E.And [
          E.Iff (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
          E.Implies (list_head l3 u, E.Or [list_head l1 u; list_head l2 u]);
        ])
  in
  let preds = ["list_member"; "list_head"] in
  match if_diff with
  | Some _ ->
    (* let _ = SpecAbd.find_weakened_model
     *     (sprintf "%s%s" bench_name which_bench) ctx mii pre spectable_post in *)
     let _ = SpecAbd.result
        (sprintf "%s%s" bench_name which_bench)
        ["concat"] spectable_post holel preds in
    ()
  | None ->
    let imps = ["Stack.is_empty", (function
        | [V.L []] -> Some [V.B true]
        | [V.L _] -> Some [V.B false]
        | _ -> raise @@ InterExn "bad prog");
       "Stack.push", push_program;
       "Stack.top", top_program;
       "Stack.tail", tail_program;
       "concat", concat_program;
      ] in
    let imp_map = List.fold_left (fun m (name, imp) ->
        StrMap.add name imp m
      ) StrMap.empty imps in
    let mii, vc, holes, spectab = Translate.trans (source, assertion1) imp_map in
    (* let total_env = SpecAbd.multi_infer ~snum:(Some 4) ~uniform_qv_num:1
     *     (sprintf "%s%s" bench_name which_bench)
     *     ctx mii pre spectable_post holel preds 1 in *)
    (* let _ = raise @@ InterExn "none" in *)
    let total_env = SpecAbd.multi_infer ~snum:(Some 4) ~uniform_qv_num:1
        (sprintf "%s%s" bench_name which_bench)
        ctx mii vc spectab holel preds 1 in
    ()
else if String.equal which_bench "2" then
  let spectable_post = set_spec (predefined_spec_tab) "concat"
      [T.IntList, "l1";T.IntList, "l2";T.IntList, "l3"]
      [T.Int, "u"; T.Int, "v"]
      (E.And [
          E.Implies(list_member l3 u, And [list_member l1 u; list_member l2 u]);
        ])
  in
  let holel = [
    is_empty_hole;
    top_hole;
    tail_hole;
    push_hole;
  ] in
  let preds = ["list_member";] in
  match if_diff with
  | Some _ ->
    (* let _ = SpecAbd.find_weakened_model
     *     (sprintf "%s%s" bench_name which_bench) ctx mii pre spectable_post in *)
    let _ = SpecAbd.result
        (sprintf "%s%s" bench_name which_bench)
        ["concat"] spectable_post holel preds in
    ()
  | None ->
    let total_env = SpecAbd.multi_infer
        (sprintf "%s%s" bench_name which_bench)
        ctx mii pre spectable_post holel preds 1 in
    ()
else if String.equal which_bench "3" then
  let spectable_post = set_spec (predefined_spec_tab) "concat"
      [T.IntList, "l1";T.IntList, "l2";T.IntList, "l3"]
      [T.Int, "u"; T.Int, "v"]
      (E.And [
          E.Iff(list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
          E.Implies(E.Or [list_order l1 u v; list_order l2 u v],
                    list_order l3 u v);
        ])
  in
  let holel = [
    is_empty_hole;
    top_hole;
    tail_hole;
    push_hole;
  ] in
  let preds = ["list_member"; "list_head"; "list_order"] in
  match if_diff with
  | Some _ ->
    (* let _ = SpecAbd.find_weakened_model
     *     (sprintf "%s%s" bench_name which_bench) ctx mii pre spectable_post in *)
    let _ = SpecAbd.result
        (sprintf "%s%s" bench_name which_bench)
        ["concat"] spectable_post holel preds in
    ()
  | None ->
    let total_env = SpecAbd.multi_infer
        (sprintf "%s%s" bench_name which_bench)
        ctx mii pre spectable_post holel preds 1 in
    ()
else if String.equal which_bench "4" then
  let spectable_post = set_spec (predefined_spec_tab) "concat"
      [T.IntList, "l1";T.IntList, "l2";T.IntList, "l3"]
      [T.Int, "u"; T.Int, "v"]
      (E.And [
          E.Implies(list_member l1 u, list_member l3 u);
        ])
  in
  let holel = [
    is_empty_hole;
    top_hole;
    tail_hole;
    push_hole;
  ] in
  let preds = ["list_member";] in
  match if_diff with
  | Some _ ->
    (* let _ = SpecAbd.find_weakened_model
     *     (sprintf "%s%s" bench_name which_bench) ctx mii pre spectable_post in *)
    let _ = SpecAbd.result
        (sprintf "%s%s" bench_name which_bench)
        ["concat"] spectable_post holel preds in
    ()
  | None ->
    let total_env = SpecAbd.multi_infer
        (sprintf "%s%s" bench_name which_bench)
        ctx mii pre spectable_post holel preds 1 in
    ()
else raise @@ InterExn "no such bench"
;;
