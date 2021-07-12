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
    Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "29999")] in
  ctx
;;

type infer_action =
  | InferConsistent
  | InferFull
  | InferWeakening

let start action sourcefile assertionfile outputdir sampling_bound timebound =
  let ctx = init () in
  let source = parse sourcefile in
  let assertion = parse assertionfile in
  (* let () = raise @@ InterExn "end" in *)
  let mii, vc, holes, preds, spectab, basic_info = Translate.trans (source, assertion) in
  let () = Core.Unix.mkdir_p (Printf.sprintf "_%s" outputdir) in
  let basic_info_filename = Printf.sprintf "_%s/_basic_info.json" outputdir in
  let () = Yojson.Basic.to_file basic_info_filename basic_info in
  let r () =
    match action, sampling_bound with
    | InferFull, Some snum ->
      SpecAbd.do_full ~snum:(Some snum) ~uniform_qv_num:1
        outputdir
        ctx mii vc spectab holes preds 1 timebound
    | InferFull, None ->
      SpecAbd.do_full
        outputdir
        ctx mii vc spectab holes preds 1 timebound
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
  match time r with
  | SpecAbd.Cex _, delta_time-> eprintf "Failed with Cex in %f(s)!\n" delta_time
  | _ , delta_time ->
    let mode_str = (match action with
        | InferFull -> "Full"
        | InferConsistent -> "Consistent"
        | InferWeakening -> "Weakening") in
    eprintf "%s inference Seccussed in %f(s)!\n" mode_str delta_time

let time_d sourcefile assertionfile outputdir =
  let ctx = init () in
  let source = parse sourcefile in
  let assertion = parse assertionfile in
  (* let () = raise @@ InterExn "end" in *)
  let mii, vc, _, _, spectab, _ = Translate.trans (source, assertion) in
  SpecAbd.find_weakened_model outputdir ctx mii vc spectab

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

let count_phi dir funcname =
  let resultfile = sprintf "_%s/_bound_maximal.json" dir in
  let oraclefile = sprintf "_%s/_oracle_maximal.json" dir in
  let open Yojson.Basic in
  let open Util in
  let aux preds spectable name =
    let spec = StrMap.find "make_single_table" spectable funcname in
    let num_oracle_fv = fst (SpecAbd.merge_spec spec preds) in
    let () = Yojson.Basic.to_file (sprintf "_%s/_count_%s.json" dir funcname)
        (`Assoc ["cat", `String name; "num_phi", `Int num_oracle_fv]) in
    printf "%i\n" num_oracle_fv
  in
  try
    let (preds, result) = Env.decode_infer_result (from_file resultfile) in
    (try
       let (_, spectable) = Env.decode_infer_result @@ from_file oraclefile in
       aux preds spectable "oracle"
       with
       | _ ->
         aux preds result "bound"
      )
  with
  | _ -> printf "cannot find %s\n" resultfile

let tpname = "nat"

let tpedvar_to_coqstr (tp, name) =
  let tp_coqstr =
    match tp with
    | T.Int -> tpname
    | T.Bool -> "bool"
    | T.IntList -> sprintf "list %s" tpname
    | T.IntTree | T.IntTreeI | T.IntTreeB -> sprintf "tree %s" tpname
  in
  sprintf "(%s:%s) " name tp_coqstr

type coqresult =
  | Consistent
  | BoundMaximal
  | OracleMaximal

let layout_coqresult = function
  | Consistent -> "consistent"
  | BoundMaximal -> "bound"
  | OracleMaximal -> "oracle"

let spec_to_coq_string funcname subtasknum spec =
  let (args, (qv, body)) = spec in
  (* let eq_str = sprintf "(eq: %s -> %s -> Prop)" tpname tpname in *)
  let make_args =
    List.fold_left (fun str x -> str ^ (tpedvar_to_coqstr x)) "" (args @ qv) in
  let spec_label = sprintf "%s_spec %s" funcname
      (List.fold_left (fun str (_, name) -> sprintf "%s %s" str name) "" args) in
  let prefix = sprintf "Lemma %s_%i %s: (%s) -> %s." funcname
      subtasknum make_args spec_label (Ast.E.layoutcoq body) in
  sprintf "%s\n" prefix

let to_coq resultfile funcname =
  let open Yojson.Basic in
  let open Util in
  let (preds, spectable) = Env.decode_infer_result (from_file resultfile) in
  let spec = StrMap.find (sprintf "to_coq: cannot find (%s)" funcname) spectable funcname in
  let args, (qv, body) =
    match spec with
    | args, (qv, (Ast.E.Or _)) ->
      (* printf "merge\n"; *)
      snd @@ SpecAbd.merge_spec spec preds
    | _ -> spec in
  let horns = List.map (fun body -> args, (qv, body)) (Ast.E.to_horns body) in
  let () = List.iteri (fun idx horn ->
      printf "%s\n" (spec_to_coq_string funcname idx horn)
    ) horns in
  ()
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
      let%map_open outputdir = anon ("outputdir" %: string)
      and time_bound = flag "-tb" (optional float) ~doc:"the time bound" in
      fun () ->
        let ctx = init () in
        try
          let (_ : SpecAbd.multi_infer_result), delta_time = time (fun () -> SpecAbd.do_weakening ctx outputdir time_bound) in
          eprintf "Weakening Inference Seccussed in %f(s)!\n" delta_time
        with
        | _ -> eprintf "No Consistent Result Found!\n"
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
      and time_bound = flag "-tb" (optional float)
          ~doc:"the time bound"
      in
      cont sourcefile assertionfile assertionfile outputdir sampling_bound time_bound
    )

let infer =
  Command.group ~summary:"inference"
    [ "consistent",
      common_parser "infer consistent specification mapping"
        (fun sourcefile assertionfile assertionfile outputdir sampling_bound timebound ->
           fun () ->
             start InferConsistent sourcefile assertionfile outputdir sampling_bound timebound);
      "full",
      common_parser "infer consistent specification mapping, then do weakening"
        (fun sourcefile assertionfile assertionfile outputdir sampling_bound timebound ->
           fun () ->
             start InferFull sourcefile assertionfile outputdir sampling_bound timebound);
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

let diff =
   Command.basic
     ~summary:"time𝑑: calculate the time needed for the SMT solver to find a sample allowed by aweakened solution but not the initial one"
    Command.Let_syntax.(
      let%map_open sourcefile = anon ("sourcefile" %: regular_file)
      and assertionfile = anon ("assertionfile" %: regular_file)
      and outputdir = anon ("outputdir" %: string)
      in
      fun () ->
         time_d sourcefile assertionfile outputdir
    )

let count =
  Command.basic
    ~summary:"|𝜙+|: count the total positive feature vectors in the space of weakenings, notice it may cost several minutes. For the blue entries, it will takes serveal hours. "
    Command.Let_syntax.(
      let%map_open outputdir = anon ("outputdir" %: string)
      and funcname = anon ("funcname" %: string)
      in
      fun () ->
        count_phi outputdir funcname
    )

let coq =
  Command.basic
    ~summary:"print the corresponding coq theorems need to be proved."
    Command.Let_syntax.(
      let%map_open resultfile = anon ("resultfile" %: regular_file)
      and funcname = anon ("funcname" %: string)
      in
      fun () -> to_coq resultfile funcname
    )

let command =
  Command.group ~summary:"Data-Driven Abductive Inference of Library Specifications"
    [ "infer", infer;
      "diff", diff;
      "count", count;
      "show", show;
      "coq", coq;
    ]

let () = Command.run command
;;
