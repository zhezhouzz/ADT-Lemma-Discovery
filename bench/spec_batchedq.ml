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
let bench_name = "batchedq" in
let ctx = init () in
let cons, cons_hole = make_hole_from_info
    {name = "ListCons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.I h; V.L t] -> Some [V.L (h :: t)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let nil, nil_hole = make_hole_from_info
    {name = "ListNil"; intps = []; outtps = [T.IntList];
     prog = function
       | [] -> Some [V.L []]
       | _ -> raise @@ InterExn "bad prog"
    } in
let is_empty, is_empty_hole = make_hole_from_info
    {name = "ListIsEmpty"; intps = [T.IntList]; outtps = [T.Bool];
     prog = function
       | [V.L []] -> Some [V.B true]
       | [V.L _ ] -> Some [V.B false]
       | _ -> raise @@ InterExn "bad prog"
    } in
let rev, rev_hole = make_hole_from_info
    {name = "ListRev"; intps = [T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L l] -> Some [V.L (List.rev l)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let f, f', r, r', f1 = map5 list_var ("f", "f'","r", "r'", "f1") in
let nu_empty = bool_var "nu_empty" in
let tail args = SpecApply ("Tail", args) in
let pre = make_match [T.IntList, "l"; T.IntList, "r"] [T.IntList, "l'"; T.IntList, "r'"]
    [(Some (cons [x;f1;f]), [T.IntList, "l"; T.IntList, "r"]),
     (Some (
         Ite(is_empty [f1;nu_empty],
             And [rev [r;f']; poly_eq [f1;r']],
             And [poly_eq [f1;f']; poly_eq [r;r'];]
            )
       ), [T.IntList, "l'"; T.IntList, "r'"]
     )
    ]
in
let mii =
  let open SpecAbd in
  {upost = tail [f;r;f';r'];
   uvars = [];
   uinputs = [T.IntList, "f"; T.IntList, "r";];
   uoutputs = [T.IntList, "f'"; T.IntList, "r'";];
   uprog = function
     | [V.L f; V.L r;] ->
       (match f, r with
        | [], _ -> None
        | _ :: f, r ->
          if List.is_empty f
          then Some [V.L (List.rev r); V.L f] else Some [V.L f; V.L r])
     | _ -> raise @@ InterExn "bad prog"
  }
in
let holel = [
  is_empty_hole;
  cons_hole;
  rev_hole;
  nil_hole] in
let which_bench = Array.get Sys.argv 1 in
let if_diff = try Some (Array.get Sys.argv 2) with _ -> None in
if String.equal which_bench "1" then
  let preds = ["list_member"; "list_head";] in
  let spectable = add_spec predefined_spec_tab "Tail"
      [T.IntList, "l1";T.IntList, "l2";T.IntList, "l3";T.IntList, "l4"]
      [T.Int, "u"]
      (E.And [
          E.Iff (Or[list_member l3 u; list_head l1 u; list_member l4 u;],
                 E.Or [list_member l1 u; list_member l2 u]);
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
  let preds = ["list_member"; "list_head"; "list_order"] in
  let spectable = add_spec predefined_spec_tab "Tail"
      [T.IntList, "l1";T.IntList, "l2";T.IntList, "l3";T.IntList, "l4"]
      [T.Int, "u"; T.Int, "v"]
      (E.And [
          E.Iff (Or[list_member l3 u; list_member l4 u; list_head l1 u],
                 E.Or [list_member l1 u; list_member l2 u]);
          E.Implies (Or[list_order l3 u v; list_order l4 v u],
                     Or[list_order l1 u v; list_order l2 v u])
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
    ();;
