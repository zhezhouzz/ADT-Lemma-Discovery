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
let tool_name = "ocamlc"
let ppf = Format.err_formatter
let parse sourcefile =
  let structure = Pparse.parse_implementation ~tool_name Format.err_formatter sourcefile in
  (* let _ = Printast.structure 0 Format.std_formatter structure in *)
  structure
;;

let start if_full sourcefile assertionfile outputdir sampling_bound =
  let ctx = init () in
  let bench_name = "customstk" in
  let source = parse sourcefile in
  let assertion = parse assertionfile in
  let mii, vc, holes, preds, spectab = Translate.trans (source, assertion) in
  let r =
  match if_full, sampling_bound with
  | true, Some snum ->
    SpecAbd.do_full ~snum:(Some snum) ~uniform_qv_num:1
      outputdir
      ctx mii vc spectab holes preds 1
  | true, None ->
    SpecAbd.do_full
      outputdir
      ctx mii vc spectab holes preds 1
  | false, Some snum ->
    SpecAbd.do_consistent ~snum:(Some snum) ~uniform_qv_num:1
      outputdir
      ctx mii vc spectab holes preds 1
  | false, None ->
    SpecAbd.do_consistent
      outputdir
      ctx mii vc spectab holes preds 1
  in
  match r with
  | SpecAbd.Cex _ -> printf "Fail with Cex!\n"
  | _ ->
    printf "Inference Seccussed!\n"

let print_help () =
  printf "help: ./main.exe full <sourcefile> <assertionfile> <outputdir> [sampling bound] \n";
  printf "      ./main.exe consistent <sourcefile> <assertionfile> <outputdir> [sampling bound]\n";
  printf "      ./main.exe weakening <outputdir>\n";
  printf "      ./main.exe show consistent <outputdir>\n";
  printf "      ./main.exe show weakening <outputdir>\n"
;;
let action =
  try
    Array.get Sys.argv 1
  with
  | _ ->
    print_help ();
    raise @@ Failure "wrong arguments"
in
match action with
| "consistent" | "full" ->
  let sourcefile, assertionfile, outputdir =
    try
      (Array.get Sys.argv 2,
       Array.get Sys.argv 3,
       Array.get Sys.argv 4)
    with
    | _ ->
      print_help ();
      raise @@ Failure "wrong arguments"
  in
  let sampling_bound = try Some (int_of_string (Array.get Sys.argv 5)) with _ -> None in
  let sampling_bound =  None in
  (match action with
   | "consistent" -> start false sourcefile assertionfile outputdir sampling_bound
   | "full" -> start true sourcefile assertionfile outputdir sampling_bound
   | _ -> raise @@ Failure "never happen"
  )
|"weakening" ->
  let outputdir =
    try
      (Array.get Sys.argv 2)
    with
    | _ ->
      print_help ();
      raise @@ Failure "wrong arguments"
  in
  let ctx = init () in
  let _ = SpecAbd.do_weakening ctx outputdir in
  printf "Weakening Inference Seccussed!\n"
| "show" ->
  let action, outputdir =
    try
      (Array.get Sys.argv 2, Array.get Sys.argv 3)
    with
    | _ ->
      print_help ();
      raise @@ Failure "wrong arguments"
  in
  (match action with
   | "consistent" ->
     let consistent_file = sprintf "_%s/_consistent.json" outputdir in
     (try
        let _, spectab = Env.decode_infer_result (Yojson.Basic.from_file consistent_file) in
        let _ = Ast.print_spectable spectab in
        ()
      with
      | _ -> printf "cannot find consistent result!")
   | "weakening" ->
     let oracle_max_file = sprintf "_%s/_oracle_maximal.json" outputdir in
     let bound_max_file = sprintf "_%s/_bound_maximal.json" outputdir in
     (try
        let _, spectab = Env.decode_infer_result (Yojson.Basic.from_file oracle_max_file) in
        let _ = Ast.print_spectable spectab in
        let _ = printf "This result is maximal.\n" in
        ()
      with
      | _ ->
        (try
           let _, spectab = Env.decode_infer_result (Yojson.Basic.from_file bound_max_file) in
           let _ = Ast.print_spectable spectab in
           let _ = printf "This result is maximal under time bound.\n" in
           ()
         with
         | _ ->
           printf "cannot find weakened result!"
        )
     )
   | _ -> raise @@ Failure "never happen"
  )
| _ ->
  print_help ();
  raise @@ Failure "wrong arguments"
;;
