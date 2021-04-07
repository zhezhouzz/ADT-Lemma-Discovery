module SpecAbd = Inference.SpecAbduction;;
module Env = Inference.Env;;
module Ast = Language.SpecAst;;
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
      sprintf "%s & $%i$ & ($%i$, $%i$) & $%i$ & $%i$ & $%i$ & $%i$ & $%.2f$"
        t.name t.num_r t.num_qv t.num_pred t.num_cex t.num_cex_fv t.num_pos t.num_pos_fv t.time in
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
  let num_oracle_fv, size_oracle = try
      let spectable = snd @@ Env.decode_infer_result @@ from_file oraclefile in
      let spec = StrMap.find "make_single_table" spectable funcname in
      let num_oracle_fv, _ = SpecAbd.merge_spec spec preds in
      Some num_oracle_fv, Some (Ast.spec_num_atom spec)
    with
    | _ -> None, None
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
    "bankersq", "BankersqCons", [1;2]; "batchedq", "ListCons", [1;2];
    "customstk", "push", [1;3];
    "leftisthp", "t", [1;2];
    "splayhp", "t", [1;2;3]; "stream", "Cons", [1;2;3];
    "rbset", "t", [1;2]; "trie", "triet", [1];
    "unbset", "t", [1;2;3]; "uniquel", "cons", [1;2];
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
else raise @@ InterExn "wrong arguments"
;;
