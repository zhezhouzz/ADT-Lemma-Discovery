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
let bench_name = "uniquel" in
let ctx = init () in
let x, x1, nu_nil, nu_set_add, nu =
  map5 list_var ("x","x1","nu_nil", "nu_set_add", "nu") in
let a, a1 =
  map_double int_var ("a", "a1") in
let nu_eq, nu_empty = map_double bool_var ("nu_eq", "nu_empty") in
let cons, cons_hole = make_hole_from_info
    {name = "cons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.I h; V.L t] -> Some [V.L (h :: t)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let nil, nil_hole = make_hole_from_info
    {name = "nil"; intps = []; outtps = [T.IntList];
     prog = function
       | [] -> Some [V.L []]
       | _ -> raise @@ InterExn "bad prog"
    } in
let set_add args = SpecApply ("SetAdd", args) in
let pre =
  Ast.make_match [T.IntList, "x";]
    [T.IntList, "nu"]
    [(Some (nil [nu_nil;];),
      [T.IntList, "nu_nil";]),
     (Some (cons [a; nu_nil; nu]),
      [(T.IntList, "nu");]);
     (Some (cons [a1;x1;x];),
      [T.IntList, "x";]),
     (Some (
         Ite(inteq [a;a1;nu_eq;],
             cons [a1;x1;nu],
             And[set_add [a;x1;nu_set_add];
                 cons [a1;nu_set_add;nu]
                ]
            )
       ),
      [(T.IntList, "nu");]);
    ]
in
let client_code a x =
  let rec set_add a x =
    match x with
    | [] -> [a]
    | a1 :: x1 ->
      if a == a1 then a1 :: x1 else a1 :: (set_add a x1)
  in
  set_add a x
in
let mii =
  let open SpecAbd in
  {upost = set_add [a;x;nu];
   uvars = [T.Int, "a"; T.Int, "a1"];
   uinputs = [T.Int, "a"; T.IntList, "x";];
   uoutputs = [T.IntList, "nu"];
   uprog = function
     | [V.I a; V.L x;] -> Some [V.L (client_code a x)]
     | _ -> raise @@ InterExn "bad prog"
  }
in
let holel =
  [nil_hole;
   cons_hole;] in
let which_bench = Array.get Sys.argv 1 in
let if_diff = try Some (Array.get Sys.argv 2) with _ -> None in
if String.equal which_bench "1" then
  let preds = ["list_member"; "list_head"; "list_once"] in
  let spectable = add_spec predefined_spec_tab "SetAdd"
      [T.Int, "x"; T.IntList, "l1";T.IntList, "l2"]
      [T.Int, "u";]
      (E.And [
          E.Iff(list_member l2 u, E.Or [int_eq u x; list_member l1 u]);
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
  let preds = ["list_member"; "list_head"; "list_once"] in
  let spectable = add_spec predefined_spec_tab "SetAdd"
      [T.Int, "x"; T.IntList, "l1";T.IntList, "l2"]
      [T.Int, "u";]
      (E.And [
          E.Implies (list_once l1 u, list_once l2 u);
          E.Iff(list_member l2 u, E.Or [int_eq u x; list_member l1 u]);
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
else if String.equal which_bench "3" then
  let preds = ["list_member"; "list_head"; "list_once"] in
  let spectable = add_spec predefined_spec_tab "SetAdd"
      [T.Int, "x"; T.IntList, "l1";T.IntList, "l2"]
      [T.Int, "u";]
      (E.And [
          E.Implies (list_member l1 u, list_once l2 u);
          E.Iff(list_member l2 u, E.Or [int_eq u x; list_member l1 u]);
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
else raise @@ InterExn "no such bench";;
