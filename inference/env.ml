module P = Pred.Pred
module V = Pred.Value
module Ast = Language.SpecAst
module Epr = Ast.E
module SE = Epr.SE
module T = Tp.Tp
module F = Feature.Feature
module FV = Sample.FeatureVector
module D = Dtree.Dtree
open Utils

type flow = {
  pre_flow: Ast.t;
  applied_args_map: (SE.t list list) StrMap.t
}

open Yojson.Basic

let encode_applied_args args =
  `List (List.map (fun args ->
      `List (List.map SE.encode args)
    ) args)

let decode_applied_args json =
  decode_list "decode_applied_args"
    (decode_list "decode_applied_args" SE.decode) json
  (* function
   * | `List l ->
   *   List.map (fun j ->
   *       match j with
   *       | `List l -> List.map SE.decode l
   *       | _ -> raise @@ InterExn "decode_applied_args"
   *     ) l
   * | _ -> raise @@ InterExn "decode_applied_args" *)

let encode_flow flow =
  let pre_flow_j = Ast.encode flow.pre_flow in
  let applied_args_map_j = StrMap.fold (fun name sell r ->
      (`Assoc ["name", `String name;
               "applied_args", encode_applied_args sell]) :: r
    ) flow.applied_args_map [] in
  `Assoc [
    "pre_flow", pre_flow_j; "applied_args_map", `List applied_args_map_j
  ]

let decode_flow json =
  let open Util in
  let j = json |> member "applied_args_map" in
  let m = StrMap.from_kv_list @@ decode_list "decode_flow" (fun json ->
      let name = json |> member "name" |> to_string in
      let sell = json |> member "applied_args" |> decode_applied_args in
      name, sell
    ) j
  in
  {pre_flow = json |> member "pre_flow" |> Ast.decode;
   applied_args_map = m
  }

type vc = {
  preds: string list;
  multi_pre: flow list;
  post: Ast.t;
  spectable: Ast.spec StrMap.t;
  vars: T.tpedvar list;
  inputs: T.tpedvar list;
  outputs: T.tpedvar list;
  prog: V.t list -> (V.t list) option;
}

let encode_vc vc =
  let preds_j = `List (List.map (fun x -> `String x) vc.preds) in
  let multi_pre_j = `List (List.map encode_flow vc.multi_pre) in
  let post_j = Ast.encode vc.post in
  let spectable_j = Ast.spectable_encode vc.spectable in
  let vars_j = `List (List.map T.tpedvar_encode vc.vars) in
  let inputs_j = `List (List.map T.tpedvar_encode vc.inputs) in
  let outputs_j = `List (List.map T.tpedvar_encode vc.outputs) in
  `Assoc [
    "preds", preds_j;
    "multi_pre", multi_pre_j;
    "post", post_j;
    "spectable", spectable_j;
    "vars", vars_j;
    "inputs", inputs_j;
    "outputs", outputs_j;
  ]

let decode_vc json =
  let open Util in
  {preds = json |> member "multi_pre" |> decode_list "decode_vc" to_string;
    multi_pre = json |> member "multi_pre" |>
               (decode_list "decode_vc" decode_flow);
   post = json |> member "post" |> Ast.decode;
   spectable = json |> member "spectable" |> Ast.spectable_decode;
   vars = json |> member "vars" |> (decode_list "decode_vc" T.tpedvar_decode);
   inputs = json |> member "inputs" |> (decode_list "decode_vc" T.tpedvar_decode);
   outputs = json |> member "outputs" |> (decode_list "decode_vc" T.tpedvar_decode);
   prog = fun _ -> None;
  }

type single_result = {
  additional_dt: int D.t;
  additional_spec: Ast.spec;
  init_dt: int D.t;
  init_spec: Ast.spec;
}

let encode_sr sr =
  let additional_dt = D.encode (fun i -> `Int i) sr.additional_dt in
  let additional_spec = Ast.spec_encode sr.additional_spec in
  let init_dt = D.encode (fun i -> `Int i) sr.init_dt in
  let init_spec = Ast.spec_encode sr.init_spec in
  `Assoc [
    "additional_dt", additional_dt;
    "additional_spec", additional_spec;
    "init_dt", init_dt;
    "init_spec", init_spec;
  ]

let decode_sr json =
  let decoder = function
    | `Int i -> i
    | _ -> raise @@ InterExn "decoder_sr"
  in
  let open Util in
  {additional_dt = json |> member "additional_dt" |> D.decode decoder;
   additional_spec = json |> member "additional_spec" |> Ast.spec_decode;
   init_dt = json |> member "init_dt" |> D.decode decoder;
   init_spec = json |> member "init_spec" |> Ast.spec_decode;
  }

type spec_env = {
  current: single_result;
  qv: T.tpedvar list;
  fset: F.t list;
  hole: Language.Helper.hole;
  unknown_fv: T.tpedvar list;
  fvtab: (bool list, D.label) Hashtbl.t;
  if_maximal: bool
}

let fv_encode fv =
  let fv = Array.of_list fv in
  `String (String.init (Array.length fv)
             (fun i -> if Array.get fv i then 't' else 'f')
          )

let fv_decode json =
  let str = Util.to_string json in
  List.rev @@ Seq.fold_left (fun fv bchar ->
      if Char.equal bchar 't' then true :: fv
      else if Char.equal bchar 'f' then false::fv
      else raise @@ InterExn "fv_decode"
    ) [] (String.to_seq str)

let fvtab_encode tab =
  let l =
  Hashtbl.fold (fun vec label l ->
      (`Assoc ["v", fv_encode vec; "l", D.label_encode label]) :: l
      ) tab [] in
  `List l

let fvtab_decode = function
  | `List l ->
    let fvtab = Hashtbl.create (2 * (List.length l)) in
    let _ = List.iter (fun json ->
        let open Util in
        let vec = json |> member "v" |> fv_decode in
        let label = json |> member "l" |> D.label_decode in
        Hashtbl.add fvtab vec label
      ) l in
    fvtab
  | _ -> raise @@ InterExn "fvtab_decode"

let encode_spec_env env =
  let current = encode_sr env.current in
  let qv = `List (List.map T.tpedvar_encode env.qv) in
  let fset = `List (List.map F.encode env.fset) in
  let hole = Language.Helper.encode_hole env.hole in
  let unknown_fv = `List (List.map T.tpedvar_encode env.unknown_fv) in
  let fvtab = fvtab_encode env.fvtab in
  let if_maximal = `Bool env.if_maximal in
  `Assoc [
    "current", current;
    "qv", qv;
    "fset", fset;
    "hole", hole;
    "unknown_fv", unknown_fv;
    "fvtab", fvtab;
    "if_maximal", if_maximal
  ]

let decode_spec_env json =
  let open Util in
  {current = json |> member "current" |> decode_sr;
   qv = json |> member "qv" |> decode_list "decode_spec_env" T.tpedvar_decode;
   fset = json |> member "fset" |> decode_list "decode_spec_env" F.decode;
   hole = json |> member "hole" |> Language.Helper.decode_hole;
   unknown_fv = json |> member "unknown_fv" |> decode_list "decode_spec_env" T.tpedvar_decode;
   fvtab = json |> member "fvtab" |> fvtab_decode;
   if_maximal = json |> member "if_maximal" |> to_bool;
  }

let encode_spec_env_list envs =
  `List (List.map encode_spec_env envs)

let decode_spec_env_list json =
  decode_list "decode_spec_env_list" decode_spec_env json

let encode_weakening (vc, envs) =
  `Assoc [
    "vc", encode_vc vc;
    "envs", encode_spec_env_list envs
  ]

let decode_weakening json =
  (json |> Util.member "vc" |> decode_vc,
   json |> Util.member "envs" |> decode_spec_env_list)

type maximal_result =
  | AlreadyMaxed of spec_env
  | MayAlreadyMaxed of spec_env
  | NewMaxed of vc * spec_env
  | Weaker of vc * spec_env

type stat = {
  start_posfv: int ref;
  start_negfv: int ref;
  start_mayfv: int ref;
  num_pos_query: int ref;
  num_z3_pos_query: int ref;
  num_pos_verify: int ref;
  num_z3_pos_verify: int ref;
  num_neg_query: int ref;
  num_z3_neg_query: int ref;
  num_weakening: int ref;
  interval: float;
  interval_past: float ref;
  (* a reverse list *)
  num_weakening_every_interval: (int list) ref;
  run_time: float ref;
  end_posfv: int ref;
  end_negfv: int ref;
  end_mayfv: int ref;
}

let stat_init ?interval:(interval = 300.0) env =
  let (p,n,m) = Hashtbl.fold (fun _ label (p,n,m) ->
      match label with
      | D.Pos -> (p+1,n,m)
      | D.MayNeg -> (p,n,m+1)
      | D.Neg -> (p,n+1,m)
    ) env.fvtab (0,0,0) in
  {start_posfv = ref p;
   start_negfv = ref n;
   start_mayfv = ref m;
   num_pos_query = ref 0;
   num_z3_pos_query = ref 0;
   num_pos_verify = ref 0;
   num_z3_pos_verify = ref 0;
   num_neg_query = ref 0;
   num_z3_neg_query = ref 0;
   num_weakening = ref 0;
   interval = interval;
   interval_past = ref 0.0;
   num_weakening_every_interval = ref [0];
   run_time = ref 0.0;
   end_posfv = ref 0;
   end_negfv = ref 0;
   end_mayfv = ref 0;
  }

let add_end_stat env stat =
  let (p,n,m) = Hashtbl.fold (fun _ label (p,n,m) ->
      match label with
      | D.Pos -> (p+1,n,m)
      | D.MayNeg -> (p,n,m+1)
      | D.Neg -> (p,n+1,m)
    ) env.fvtab (0,0,0) in
  (stat.end_posfv := p;
   stat.end_negfv := n;
   stat.end_mayfv := m;
  )

let encode_stat stat =
  `Assoc [
    "start_posfv", `Int !(stat.start_posfv);
    "start_negfv", `Int !(stat.start_negfv);
    "start_mayfv", `Int !(stat.start_mayfv);
    "num_pos_query", `Int !(stat.num_pos_query);
    "num_z3_pos_query", `Int !(stat.num_z3_pos_query);
    "num_pos_verify", `Int !(stat.num_pos_verify);
    "num_z3_pos_verify", `Int !(stat.num_z3_pos_verify);
    "num_neg_query", `Int !(stat.num_neg_query);
    "num_z3_neg_query", `Int !(stat.num_z3_neg_query);
    "num_weakening", `Int !(stat.num_weakening);
    "interval", `Float stat.interval;
    "interval_past", `Float !(stat.interval_past);
    "num_weakening_every_interval", `List (List.map (fun x -> `Int x)
                                             !(stat.num_weakening_every_interval));
    "run_time", `Float !(stat.run_time);
    "end_posfv", `Int !(stat.end_posfv);
    "end_negfv", `Int !(stat.end_negfv);
    "end_mayfv", `Int !(stat.end_mayfv);
  ]

let save_stat benchname fname time_bound stat =
  let name =
    match time_bound with
    | None -> Printf.sprintf "%s%s_%s_stat.json" benchname fname "none"
    | Some f -> Printf.sprintf "%s%s_%f_stat.json" benchname fname f
  in
  Yojson.Basic.to_file name (encode_stat stat)

type consistent_stat_once = {
  num_qv: int;
  num_pos_refine: int ref;
  num_fv_of_samples: int ref;
  num_cex: int ref;
  num_fv_of_cex: int ref;
  run_time: float ref;
}

let init_consistent_stat_once num_qv =
  {num_qv = num_qv;
   num_pos_refine = ref 0;
   num_fv_of_samples = ref 0;
   num_cex = ref 0;
   num_fv_of_cex = ref 0;
   run_time = ref 0.0;
  }

(* let add_end_stat_once env stat =
 *   let (p,n,m) = Hashtbl.fold (fun _ label (p,n,m) ->
 *       match label with
 *       | D.Pos -> (p+1,n,m)
 *       | D.MayNeg -> (p,n,m+1)
 *       | D.Neg -> (p,n+1,m)
 *     ) env.fvtab (0,0,0) in
 *   (stat.end_posfv := p;
 *    stat.end_negfv := n;
 *    stat.end_mayfv := m;
 *   ) *)

let encode_consistent_stat_once stat =
  `Assoc [
    "num_qv", `Int (stat.num_qv);
    "num_pos_refine", `Int !(stat.num_pos_refine);
    "num_fv_of_samples", `Int !(stat.num_fv_of_samples);
    "num_cex", `Int !(stat.num_cex);
    "num_fv_of_cex", `Int !(stat.num_fv_of_cex);
    "run_time", `Float !(stat.run_time);
  ]

type consistent_stat = {
  consist_list: (consistent_stat_once list) ref;
}

let init_consistent_stat () =
  {consist_list = ref [];}

let encode_consistent_stat stat =
  `Assoc [
    "consist_list", `List (List.map encode_consistent_stat_once !(stat.consist_list));
  ]

let save_consistent_stat benchname stat =
  let name = Printf.sprintf "%s_consistent_stat.json" benchname in
  Yojson.Basic.to_file name (encode_consistent_stat stat)


let encode_infer_result (preds, spectable) =
  `Assoc [
    "preds", `List (List.map (fun x -> `String x) preds);
    "spectable", Ast.spectable_encode spectable;
  ]

let decode_infer_result json =
  let open Util in
  let preds = json |> member "preds" |> decode_list "decode_infer_result" to_string in
  let spectable = json |> member "spectable" |> Ast.spectable_decode in
  (preds, spectable)

let encode_single_infer_result (preds, sr) =
  `Assoc [
    "preds", `List (List.map (fun x -> `String x) preds);
    "sr", encode_sr sr;
  ]

let decode_single_infer_result json =
  let open Util in
  let preds = json |> member "preds" |> decode_list "decode_single_infer_result" to_string in
  let sr = json |> member "sr" |> decode_sr in
  (preds, sr)
