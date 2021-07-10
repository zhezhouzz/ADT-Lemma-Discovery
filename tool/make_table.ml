module SpecAbd = Inference.SpecAbduction;;
module Env = Inference.Env;;
module Ast = Language.SpecAst;;
module Epr = Ast.E;;
module T = Tp.Tp;;
open Printf;;
open Utils;;
type table = {
  name: string;
  num_qv: int;
  num_pred: int;
  num_r : int;
  num_cex: int;
  num_cex_fv: int;
  num_pos: int;
  num_pos_fv: int;
  time: float;
  size: int option;
}
let write_table table =
  let line t =
    let str =
      sprintf "%s & $%i$ & ($%i$, $%i$) & $%i$ & $%.2f$"
        t.name t.num_r t.num_qv t.num_pred t.num_cex t.time in
    match t.size with
    | None -> sprintf "%s & none" str
    | Some s -> sprintf "%s & %i" str s in
  let str = List.fold_left (fun str t ->
      match str with
      | None -> Some (line t)
      | Some str -> Some (sprintf "%s \\\\\n%s" str (line t))) None table in
  match str with
  | None -> " \\"
  | Some str -> str

let read_table benchname num =
  let cstatfile = sprintf "_%s%i/_consistent_stat.json" benchname num in
  let cresultfile = sprintf "_%s%i/_consistent.json" benchname num in
  let open Yojson.Basic in
  let open Util in
  let get_pnum_size resultjson =
    let (preds, result) = Env.decode_infer_result resultjson in
    let num_r = StrMap.cardinal result in
    let sizes = StrMap.fold (fun _ spec s ->
        s + (Ast.spec_num_atom spec)
      ) result 0 in
    (List.length preds), num_r, Some sizes
  in
  let pnum, num_r, size =
    try get_pnum_size (from_file cresultfile) with
    | _ -> 2, 2, None in
  let statjson = from_file cstatfile in
  let l = statjson |> member "consist_list" in
  match l with
  | `List statjson ->
    let statjson = List.last statjson in
    { name = sprintf "%s-%i" benchname num;
      num_qv = statjson |> member "num_qv" |> to_int;
      num_pred = pnum;
      num_r = num_r;
      num_cex = statjson |> member "num_cex" |> to_int;
      num_cex_fv = statjson |> member "num_fv_of_cex" |> to_int;
      num_pos = statjson |> member "num_pos_sample_violate_spec" |> to_int;
      num_pos_fv = statjson |> member "num_fv_of_samples" |> to_int;
      time = statjson |> member "run_time" |> to_float;
      size = size;
    }
  | _ -> raise @@ InterExn "read_table"

type status = Maxed | Weaker
type single_table = {
  name: string;
  status: status;
  num_weaken: int;
  num_oracle: int option;
  num_pos_fv: int;
  num_false_pos_fv: int option;
  num_oracle_fv: int option;
  time: float;
  time_oracle: float option;
  size: int;
  size_oracle: int option;
}

let status_layout = function
  | Maxed -> "maxed"
  | Weaker -> "weaker"

let make_single_table benchname num funcname =
  let statfile = sprintf "_remote_result/_%s%i/%s_3600.000000_stat.json"
      benchname num funcname in
  let ostatfile = sprintf "_remote_result/_%s%i/%s_none_stat.json"
      benchname num funcname in
  let resultfile = sprintf "_remote_result/_%s%i/_bound_maximal.json" benchname num in
  let oraclefile = sprintf "_remote_result/_%s%i/_oracle_maximal.json" benchname num in
  let open Yojson.Basic in
  let open Util in
  let statjson = from_file statfile in
  let (preds, result) = Env.decode_infer_result (from_file resultfile) in
  let bound_spec = StrMap.find "make_single_table" result funcname in
  let c = fst (SpecAbd.merge_spec bound_spec preds) in
  let _ = Printf.printf "%s %i %i\n" benchname num c in
  (* let _ = raise @@ InterExn "end" in *)
  let num_oracle_fv, size_oracle = try
      let spectable = snd @@ Env.decode_infer_result @@ from_file oraclefile in
      let spec = StrMap.find "make_single_table" spectable funcname in
      let num_oracle_fv, _ = SpecAbd.merge_spec spec preds in
      Some num_oracle_fv, Some (Ast.spec_num_atom spec)
    with
    | _ -> Some (fst (SpecAbd.merge_spec bound_spec preds)), None
  in
  let bound_time = statjson |> member "run_time" |> to_float in
  let num_weaken = statjson |> member "num_weakening" |> to_int in
  let weak_num_false_pos_fv = statjson |> member "end_negfv" |> to_int in
  let status, num_oracle, num_false_pos_fv, time_oracle, size_oracle = try
      let ostatjson = from_file ostatfile in
      let num_oracle = num_weaken + (ostatjson |> member "num_weakening" |> to_int) in
      let num_false_pos_fv = ostatjson |> member "end_negfv" |> to_int in
      (* let num_oracle_fv = ostatjson |> member "end_negfv" |> to_int in *)
      let run_time = bound_time +. (ostatjson |> member "run_time" |> to_float) in
      Weaker, Some num_oracle, Some num_false_pos_fv, Some run_time, size_oracle with
  | _ -> Maxed, None, Some weak_num_false_pos_fv, None, None
  in
  { name = sprintf "%s-%i" benchname num;
    status = status;
    num_weaken = num_weaken;
    num_oracle = num_oracle;
    num_pos_fv = statjson |> member "end_posfv" |> to_int;
    num_false_pos_fv = num_false_pos_fv;
    num_oracle_fv = num_oracle_fv;
    time = bound_time;
    time_oracle = time_oracle;
    size = Ast.spec_num_atom bound_spec;
    size_oracle = size_oracle;
  }

let write_single_table table =
  let handle_int_option x = match x with
    | None -> "none"
    | Some n -> string_of_int n
  in
  let handle_float_option x = match x with
    | None -> "none"
    | Some n -> sprintf "%.1f" n
  in
  let line t =
    sprintf "%s & %s & $%i/%s$ & $%i/%s$ & $%s$ & $%.1f/%s$ & $%i/%s$"
      t.name
      (status_layout t.status)
      t.num_weaken (handle_int_option t.num_oracle)
      t.num_pos_fv (handle_int_option t.num_oracle_fv) (handle_int_option t.num_false_pos_fv)
      t.time (handle_float_option t.time_oracle)
      t.size (handle_int_option t.size_oracle)
  in
  let str = List.fold_left (fun str t ->
      match str with
      | None -> Some (line t)
      | Some str -> Some (sprintf "%s \\\\\n%s" str (line t))) None table in
  match str with
  | None -> " \\"
  | Some str -> str

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

let spec_to_coq_string benchname num funcname tacticname mode subtasknum spec =
  let (args, (qv, body)) = spec in
  (* let eq_str = sprintf "(eq: %s -> %s -> Prop)" tpname tpname in *)
  let make_args =
    List.fold_left (fun str x -> str ^ (tpedvar_to_coqstr x)) "" (args @ qv) in
  let spec_label = sprintf "%s_spec %s" tacticname
      (List.fold_left (fun str (_, name) -> sprintf "%s %s" str name) "" args) in
  let prefix = sprintf "Lemma %s%i%s_%s%i %s: (%s) -> %s."
      benchname num (layout_coqresult mode) funcname
      subtasknum make_args spec_label (Epr.layoutcoq body) in
  (* let _ = printf "qv: %i\n" (List.length qv) in *)
  let proof =
    if List.length qv > 1
    then sprintf "Proof. solve_%s; try (assert (u_0 = u_1); subst; eauto). Qed." tacticname
    else sprintf "Proof. solve_%s. Qed." tacticname
  in
  sprintf "%s\n%s\n" prefix proof

let save_coq_file benchname num funcname tacticname mode spec =
  let args, (qv, body) = spec in
  let horns = List.map (fun body -> args, (qv, body)) (Epr.to_horns body) in
  let oc = open_out (sprintf "coq/Verify%s%i%s%s.v"
                       benchname num (layout_coqresult mode) funcname) in
  let _ = fprintf oc "Require Import ListAux.\nRequire Import TreeAux.\n" in
  let _ = List.iteri (fun idx horn ->
      fprintf oc "%s\n" (spec_to_coq_string benchname num funcname tacticname mode idx horn)
    ) horns in
  close_out oc
;;
(* let ctx =
 *   Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")] in *)
let commandline = Array.get Sys.argv 1 in
if String.equal commandline "consistent" then
  let info = ["bankersq",2 ; "batchedq", 2;
              "customstk", 4; "leftisthp", 2;
              "splayhp", 3; "stream", 3;
              "rbset", 2; "trie", 1;
              "unbset", 4; "uniquel", 2;
             ] in
  let make_lines info =
    let rec aux c benchname num =
      if c > num then [] else (read_table benchname c) :: (aux (c + 1) benchname num)
    in
    let table = List.fold_left (fun ts (benchname, num) ->
        ts @ (aux 1 benchname num)) [] info in
    let table_str = write_table table in
    let _ = printf "%s\n" table_str in
    ()
  in
  let _ = make_lines info in
  ()
else if String.equal commandline "single" then
  let info = [
    (* "bankersq", "BankersqCons", [1;2]; "batchedq", "ListCons", [1;2];
     * "customstk", "push", [1;3];
     * "leftisthp", "t", [1;2]; *)
    (* "splayhp", "t", [1;2;3]; *)
    (* "stream", "Cons", [1;2;3]; *)
    (* "rbset", "t", [1;2]; *)
    (* "trie", "triet", [1];
     * "unbset", "t", [1;2;3]; "uniquel", "cons", [1;2]; *)
    "splayhp", "t", [2;3];
    "rbset", "t", [2];
  ] in
  let make_lines info =
    let table = List.fold_left (fun ts (benchname, funcname, nums) ->
        List.fold_left (fun ts num ->
            ts @ [make_single_table benchname num funcname]
          ) ts nums) [] info in
    let table_str = write_single_table table in
    let _ = printf "%s\n" table_str in
    ()
  in
  let _ = make_lines info in
  ()
else if String.equal commandline "coq" then
  (* let info_consistent = [
   *   (\* "bankersq", "BankersqCons", "push", [1;2];
   *    * "batchedq", "ListCons", "push", [1;2];
   *    * "customstk", "push", "push", [1;3];
   *    * "stream", "Cons", "push", [1;2;3];
   *    * "uniquel", "cons", "push", [1;2]; *\)
   *   (\* "leftisthp", "t", "t", [2]; *\)
   *   (\* "unbset", "t", "t", [1;2;3]; *\)
   *   (\* "splayhp", "t", "t", [1]; *\)
   *   "rbset", "t", "t", [1;2];
   *   (\* "rbset", "t", [1;2]; "trie", "triet", [1]; *\)
   * ] in *)
  let info_bound = [
    (* "customstk", "push", "push", [1];
     * "stream", "Cons", "push", [3]; *)
    "leftisthp", "maket", "t", [1];
    "splayhp", "t", "t", [2;3];
  ] in
  let open Yojson.Basic in
  let solve mode info =
    List.iter (fun (benchname, funcname, tacticname, nums) ->
        List.iter (fun num ->
            let resultfile =
              match mode with
              | Consistent ->
                sprintf "_remote_result/_%s%i/_consistent.json" benchname num
              | BoundMaximal ->
                sprintf "_remote_result/_%s%i/_bound_maximal.json" benchname num
              | OracleMaximal ->
                sprintf "_remote_result/_%s%i/_oracle_maximal.json" benchname num
            in
            let (preds, result) = Env.decode_infer_result (from_file resultfile) in
            let spec = StrMap.find "coq" result funcname in
            let spec = match mode with
              | Consistent -> spec
              | _ -> snd @@ SpecAbd.merge_spec spec preds in
            let _ = save_coq_file benchname num funcname tacticname mode spec in
            ()
          )
          nums
      ) info
  in
  (* let _ = solve Consistent info_consistent in *)
  let _ = solve BoundMaximal info_bound in
  ()
else if String.equal commandline "merge" then
  let info_bound = [
    "customstk", 1;
    "stream", 3;
    "leftisthp", 1;
    "leftisthp", 2;
    "splayhp", 2;
    "splayhp", 3;
    "rbset", 2;
    (* "stream", 1; *)
    (* "leftisthp", "maket", "t", [1];
     * "splayhp", "t", "t", [2;3]; *)
  ] in
  let merge (benchname, num) =
    let ctx =
      Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "19999")] in
    let resultfilename = sprintf "_remote_result/_%s%i/_bound_maximal.json"
        benchname num in
    let consistentfilename = sprintf "_remote_result/_%s%i/_consistent.json" benchname num in
    let output = sprintf "_remote_result/_%s%i/_bound_maximal_merged.json" benchname num in
    let _ = Printf.printf "%s %i\n" benchname num in
    let _ = SpecAbd.smt_merge_spectable ctx consistentfilename resultfilename output in
    () in
  let _ = List.iter (fun info -> merge info) info_bound in
  ()
else raise @@ InterExn "wrong arguments"
;;
