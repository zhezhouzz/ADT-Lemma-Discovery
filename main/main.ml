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
;;
let tool_name = "ocamlc"
let ppf = Format.err_formatter
let parse sourcefile =
  let structure = Pparse.parse_implementation ~tool_name Format.err_formatter sourcefile in
  (* let _ = Printast.structure 0 Format.std_formatter structure in *)
  structure

let init () =
  let _ : unit = Random.init 0 in
  let ctx =
    Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "19999")] in
  ctx
;;

type infer_action =
  | InferConsistent
  | InferFull
  | InferWeakening

let start action sourcefile assertionfile outputdir sampling_bound =
  let ctx = init () in
  let bench_name = "customstk" in
  let source = parse sourcefile in
  let assertion = parse assertionfile in
  (* let () = raise @@ InterExn "end" in *)
  let mii, vc, holes, preds, spectab = Translate.trans (source, assertion) in
  let r =
    match action, sampling_bound with
    | InferFull, Some snum ->
      SpecAbd.do_full ~snum:(Some snum) ~uniform_qv_num:1
        outputdir
        ctx mii vc spectab holes preds 1
    | InferFull, None ->
      SpecAbd.do_full
        outputdir
        ctx mii vc spectab holes preds 1
    | InferConsistent, Some snum ->
      SpecAbd.do_consistent ~snum:(Some snum) ~uniform_qv_num:1
        outputdir
        ctx mii vc spectab holes preds 1
    | InferConsistent, None ->
      SpecAbd.do_consistent
        outputdir
        ctx mii vc spectab holes preds 1
    | InferWeakening, _ -> raise @@ InterExn "never happen"
  in
  match r with
  | SpecAbd.Cex _ -> eprintf "Fail with Cex!\n"
  | _ ->
    eprintf "Inference Seccussed!\n"

let fallback_load outputdir =
  let oracle_max_file = sprintf "_%s/_oracle_maximal.json" outputdir in
  let bound_max_file = sprintf "_%s/_bound_maximal.json" outputdir in
  try
    let preds, spectab = Env.decode_infer_result (Yojson.Basic.from_file oracle_max_file) in
    false, preds, spectab
  with
  | _ -> try
      let preds, spectab = Env.decode_infer_result (Yojson.Basic.from_file bound_max_file) in
      true, preds, spectab
    with
    | _ -> raise @@ Failure "cannot find weakened result!"

;;

open Core

let regular_file =
  Command.Arg_type.create (fun filename ->
      match Sys.is_file filename with
      | `Yes -> filename
      | `No -> failwith "Not a regular file"
      | `Unknown -> failwith "Could not determine if this was a regular file")

let infer_action =
  Command.Arg_type.create (fun infer_action ->
      match infer_action with
      | "consistent" -> InferConsistent
      | "full" -> InferFull
      | "weakening" -> InferWeakening
      | _ -> failwith "unknown inference action"
    )

let infer_weakening =
  Command.basic
    ~summary:"weaken inferred specification mapping"
    Command.Let_syntax.(
      let%map_open outputdir = anon ("outputdir" %: string) in
      fun () ->
        let ctx = init () in
        let _ : SpecAbd.multi_infer_result = SpecAbd.do_weakening ctx outputdir in
        eprintf "Weakening Inference Seccussed!\n"
    )

let common_parser doc cont =
  Command.basic
    ~summary:doc
    Command.Let_syntax.(
      let%map_open sourcefile = anon ("sourcefile" %: regular_file)
      and assertionfile = anon ("assertionfile" %: regular_file)
      and outputdir = anon ("outputdir" %: string)
      and sampling_bound = flag "-sb" (optional int)
                             ~doc:"the sampling number bound"
      in
      cont sourcefile assertionfile assertionfile outputdir sampling_bound
    )

let infer =
  Command.group ~summary:"inference"
    [ "consistent",
      common_parser "infer consistent specification mapping"
        (fun sourcefile assertionfile assertionfile outputdir sampling_bound ->
           fun () ->
           start InferConsistent sourcefile assertionfile outputdir sampling_bound);
      "full",
      common_parser "infer consistent specification mapping, then do weakening"
        (fun sourcefile assertionfile assertionfile outputdir sampling_bound ->
           fun () ->
           start InferFull sourcefile assertionfile outputdir sampling_bound);
      "weakening", infer_weakening
    ]

let show_consistent =
  Command.basic
    ~summary:"show consistent result(if exists)"
    Command.Let_syntax.(
      let%map_open outputdir = anon ("outputdir" %: string)
      in
      fun () ->
        let consistent_file = sprintf "_%s/_consistent.json" outputdir in
        (try
           let _, spectab = Env.decode_infer_result (Yojson.Basic.from_file consistent_file) in
           let () = Ast.print_spectable spectab in
           ()
         with
         | _ -> failwith "cannot find consistent result!")
    )

let show_weakening =
  Command.basic
    ~summary:"show maximal result(if exists)"
    Command.Let_syntax.(
      let%map_open outputdir = anon ("outputdir" %: string)
      and if_simplify = flag "-s" no_arg ~doc:" simplify the inferred maximal specification mapping."
      in
      fun () ->
        let if_bound, preds, spectab = fallback_load outputdir in
        let () = match if_simplify with
          | true ->
            Ast.print_spectable (SpecAbd.merge_spectable spectab preds)
          | _ ->
            Ast.print_spectable spectab
        in
        let () = if if_bound
          then eprintf "This result is maximal under time bound.\n"
          else eprintf "This result is maximal.\n"
        in
        ()
    )


let show =
  Command.group ~summary:"show"
    [ "consistent", show_consistent;
      "weakening", show_weakening
    ]

let command =
  Command.group ~summary:"Data-Driven Abductive Inference of Library Specifications"
    [ "infer", infer;
      "show", show;
    ]

let () = Command.run command
;;
