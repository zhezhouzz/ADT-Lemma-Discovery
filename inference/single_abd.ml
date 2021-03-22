module P = Pred.Pred
module V = Pred.Value
module Ast = Language.SpecAst
module Epr = Ast.E
module SE = Epr.SE
module S = Solver
module T = Tp.Tp
module F = Feature.Feature
module FV = Sample.FeatureVector
module D = Dtree.Dtree
open Utils
open Z3
open Env
open Language.Helper

let unknown_fv_fset_to_epr fset unknown_fv =
  let unknown_fv_se = List.map SE.from_tpedvar unknown_fv in
  let l =
  List.map (fun (f, b) ->
      Epr.Iff (F.to_epr f, Epr.Atom b)
      ) (List.combine fset unknown_fv_se)
  in
  Epr.And l

let default_spec = [], Epr.True

let rm_hole_from_spectab m hole =
  StrMap.update hole.name (fun v ->
      match v with
      | Some _ -> Some default_spec
      | None -> raise @@ InterExn "rm_hole_from_spectab"
    ) m

let default_constrint = Boolean.mk_true

let get_increamental_body sr =
  let _, (_, init_body) = sr.init_spec in
  let _, (_, additional_body) = sr.additional_spec in
  Epr.Or [init_body; additional_body]

let get_increamental_spec sr =
  let args, (qv, init_body) = sr.init_spec in
  let _, (_, additional_body) = sr.additional_spec in
  args, (qv, Epr.Or [init_body; additional_body])

let make_spec_with_unknown env =
  let fv_epr = unknown_fv_fset_to_epr env.fset env.unknown_fv in
  let body = get_increamental_body env.current in
  let spec = env.hole.args,
             (env.qv,
              Epr.And [Epr.Or [body; fv_epr];]) in
  spec

let make_spec_with_fv env fv =
  let fv_epr = Epr.And (List.map (fun (f, b) ->
      if b then F.to_epr f else Epr.Not (F.to_epr f)
    ) (List.combine env.fset fv)) in
  let body = get_increamental_body env.current in
  let spec = env.hole.args,
             (env.qv,
              Epr.And [Epr.Or [body; fv_epr];]) in
  spec

let fv_not_in_curr_constraint env =
  let args_e = List.map (fun v -> Epr.Atom (SE.from_tpedvar v)) env.unknown_fv in
  let init_body = D.to_epr_idx env.current.init_dt args_e in
  let additional_body = D.to_epr_idx env.current.additional_dt args_e in
  Epr.Not (Epr.Or [init_body; additional_body])

let fv_no_repeat env =
  let unknown_fv_e = List.map (fun fv -> Epr.Atom (SE.from_tpedvar fv)) env.unknown_fv in
  let c = Hashtbl.fold (fun k v l ->
      match v with
      | D.Neg ->
        let c =
          Epr.And (List.map (fun (arg, b) ->
          if b then arg else Epr.Not arg
            ) (List.combine unknown_fv_e k))
        in
        c :: l
      | D.Pos | D.MayNeg -> l
    ) env.fvtab [] in
  let c = Epr.Not (Epr.Or c) in
  c

let pos_query ctx vc_env env =
  let pre = Ast.Or (List.map (fun flow -> flow.pre_flow) vc_env.multi_pre) in
  let spec = make_spec_with_unknown env in
  let new_spectable = StrMap.update env.hole.name
      (fun v -> match v with
         | None -> raise @@ InterExn "never happen multi_apply_constraint"
         | Some _ -> Some spec)
      vc_env.spectable in
  let pos_phi = Ast.to_z3 ctx (Ast.Implies (pre, vc_env.post)) new_spectable in
  let force_enum_neg = Epr.to_z3 ctx
      (fv_not_in_curr_constraint env) in
  let force_no_repeat = Epr.to_z3 ctx @@ fv_no_repeat env in
  let pos_query = Boolean.mk_and ctx [pos_phi; force_enum_neg; force_no_repeat] in
  (* let _ = Printf.printf "pos_query:\n%s\n" (Expr.to_string pos_query) in *)
  match S.check ctx pos_query with
  | S.SmtUnsat -> None
  | S.Timeout -> raise (InterExn "pos query time out!")
  | S.SmtSat m ->
    let fv = S.get_unknown_fv ctx m env.unknown_fv in
    let _ = Printf.printf "may pos:fv = %s\n" (boollist_to_string fv) in
    Some fv

open Printf

type smt_status = Pass | NeedRefine

let gather_neg_fvec_to_tab_flow ctx env applied_args qvrange model =
    let se_range = List.map (fun x -> SE.Literal (T.Int, SE.L.Int x)) qvrange in
    let sub_assignment = List.map (fun _ -> se_range) env.qv in
    let _, names = List.split (env.hole.args @ env.qv) in
    let counter = ref 0 in
    let _ =
      List.map (fun args ->
          let args = List.map SE.from_tpedvar args in
          let extract_fvec _ values =
            let vec = List.map
                (fun feature ->
                   Epr.subst (F.to_epr feature) names (args @ values)) env.fset in
            (* let _ = printf "[vec]:%s\n" (List.to_string Epr.layout vec) in *)
            let vec' = List.map (fun e -> S.get_pred model (Epr.to_z3 ctx e)) vec in
            (* let _ = printf "[vec]:%s%s\n" (List.to_string Epr.layout vec)
             *     (boollist_to_string vec') in *)
            match Hashtbl.find_opt env.fvtab vec' with
            | Some D.Neg -> raise @@ InterExn "never happen single gather"
            | Some D.Pos | Some D.MayNeg -> ()
            | None ->
              let _ = counter := !counter + 1 in
              (* Hashtbl.add env.fvtab vec' D.MayNeg *)
              if D.exec_vector_idx env.current.init_dt vec'
              then Hashtbl.add env.fvtab vec' D.Pos
              else Hashtbl.add env.fvtab vec' D.MayNeg
          in
          let _ = List.choose_list_list_order_fold extract_fvec () sub_assignment in
          ()
        ) applied_args in
    let _ = if !counter == 0
      then raise @@ InterExn "never happen gather neg single abd" else () in
    ()

let gather_neg_fvec_to_tab ctx vc_env env qvrange model =
  List.iter (fun flow ->
      let applied_args = StrMap.find
          "[single] gather_neg_fvec_to_tab" flow.applied_args_map env.hole.name
      in
      gather_neg_fvec_to_tab_flow ctx env applied_args qvrange model
    )
  vc_env.multi_pre

let pos_verify_flow ctx vc_env env flow fv =
  let spec = make_spec_with_fv env fv in
  let new_spectable = StrMap.update env.hole.name
      (fun v -> match v with
         | None -> raise @@ InterExn "never happen multi_apply_constraint"
         | Some _ -> Some spec)
      vc_env.spectable in
  let neg_phi = Ast.to_z3 ctx
      (Ast.Not (Ast.Implies (flow.pre_flow, vc_env.post))) new_spectable in
  (* let _ = Printf.printf "verify:%s\n" (Expr.to_string neg_phi) in *)
  let if_pos =
    match S.check ctx neg_phi with
    | S.SmtUnsat ->
      (* let _ = Printf.printf "real pos[%s]\n" (boollist_to_string fv) in *)
      true
    | S.Timeout -> raise (InterExn "verify candidate pos time out!")
    | S.SmtSat _ ->
      let _ = Printf.printf "false pos[%s]\n" (boollist_to_string fv) in
      false
  in
  if_pos

let pos_verify_update_env ctx vc_env env fv =
  let res = List.map (fun flow ->
      pos_verify_flow ctx vc_env env flow fv
    ) vc_env.multi_pre in
  let if_pos = List.for_all (fun b -> b) res in
  let _ =
    match Hashtbl.find_opt env.fvtab fv, if_pos with
    | Some D.Pos, b ->
      (* let _ = Hashtbl.iter (fun vec label ->
       *     printf "%s -> <%s>\n" (boollist_to_string vec) (D.layout_label label)
       *   ) env.fvtab in *)
      raise @@ InterExn (sprintf "never happen in single abduction(%s,%b)"
                           (D.layout_label D.Pos) b)
    | Some D.Neg, b ->
      raise @@ InterExn (sprintf "never happen in single abduction(%s,%b)"
                           (D.layout_label D.Neg) b)
    | Some D.MayNeg, true ->
      Hashtbl.replace env.fvtab fv D.Pos
    | Some D.MayNeg, false | None, false ->
      Hashtbl.replace env.fvtab fv D.Neg
    | None, true ->
      Hashtbl.add env.fvtab fv D.Pos
  in
  if_pos

let body_to_spec env body =
  env.hole.args, (env.qv, body)

let summary_fv_num env =
  let pos_num = ref 0 in
  let neg_num = ref 0 in
  let mayneg_num = ref 0 in
  let _ = Hashtbl.iter (fun _ label ->
      match label with
      | D.Pos -> pos_num := !pos_num + 1
      | D.Neg -> neg_num := !neg_num + 1
      | D.MayNeg -> mayneg_num := !mayneg_num + 1
    ) env.fvtab in
  let _ = printf "{pos:%i; neg:%i; maynge:%i}\n" !pos_num !neg_num !mayneg_num in
  ()

let is_pass = function
  | Pass -> true
  | _ -> false

let neg_query ctx vc_env env new_sr =
  let counter = ref 0 in
  let rec loop new_sr =
    let new_spectable = StrMap.update env.hole.name
        (fun v -> match v with
           | None -> raise @@ InterExn "never happen multi_apply_constraint"
           | Some _ -> Some (get_increamental_spec new_sr))
        vc_env.spectable in
    let once flow =
      let neg_phi = Ast.to_z3 ctx
        (Ast.Not (Ast.Implies (flow.pre_flow, vc_env.post))) new_spectable in
      (* let _ = Printf.printf "neg_query ast:%s\n"
       *   (Ast.vc_layout (Ast.Not (Ast.Implies (flow.pre_flow, vc_env.post)))) in
       * let _ = StrMap.iter (fun name spec ->
       *   printf "%s\n" (Ast.layout_spec_entry name spec)
       * ) new_spectable in
       * let _ = Printf.printf "neg_query:%s\n" (Expr.to_string neg_phi) in *)
      match S.check ctx neg_phi with
      | S.SmtUnsat -> Pass
      | S.Timeout ->
        let _ = Printf.printf "neg_query:%s\n" (Expr.to_string neg_phi) in
        raise (InterExn "neg query time out!")
      | S.SmtSat m ->
        let bounds = S.get_preds_interp m in
        let applied_args = StrMap.find "gather_neg_fvec_to_tab_flow"
            flow.applied_args_map env.hole.name in
        let _ = gather_neg_fvec_to_tab_flow ctx env applied_args bounds m in
        (* let _ = Hashtbl.iter (fun vec label ->
         *     printf "%s:%s\n" (boollist_to_string vec) (D.layout_label label)
         *   ) env.fvtab in *)
        let _ = summary_fv_num env in
        NeedRefine
    in
    let res = List.map once vc_env.multi_pre in
    if List.for_all is_pass res
    then (if !counter == 0 then Pass else NeedRefine)
    else
      let dt, dt_idx =
        if Hashtbl.length env.fvtab == 0
        then D.T, D.T
        else D.classify_hash env.fset env.fvtab in
      let learned = body_to_spec env @@ Epr.simplify_ite @@ D.to_epr dt in
      let new_sr' = {new_sr with additional_dt = dt_idx; additional_spec = learned} in
      let _ = counter := !counter + 1 in
      loop new_sr'
  in
  loop new_sr

(* let learn_weaker ctx vc_env env =
 *   let current = StrMap.find "never happen learn_weaker"
 *       vc_env.spectable env.hole.name in
 *   let _, (_, cur_body) = current in
 *   let fset_z3 = List.map (fun f -> Epr.to_z3 ctx @@ F.to_epr f) env.fset in
 *   let rec loop () =
 *     let dt, dt_idx =
 *       if Hashtbl.length env.fvtab == 0
 *       then D.T, D.T
 *       else D.classify_hash env.fset env.fvtab in
 *     let learned_body = Epr.simplify_ite @@ D.to_epr dt in
 *     let query = Epr.to_z3 ctx @@ Epr.Not (Epr.Implies (cur_body, learned_body)) in
 *     match S.check ctx query with
 *     | S.SmtUnsat -> body_to_spec env learned_body, dt_idx
 *     | S.Timeout -> raise (InterExn "old pos time out!")
 *     | S.SmtSat m ->
 *       let fv = List.map (fun feature -> S.get_pred m feature) fset_z3 in
 *       let _ = Printf.printf "old pos[%s]\n" (boollist_to_string fv) in
 *       let _ =
 *         match Hashtbl.find_opt env.fvtab fv with
 *         | Some D.MayNeg -> Hashtbl.replace env.fvtab fv D.Pos
 *         | Some label -> raise @@ InterExn
 *             (sprintf "learn_weaker(exists %s -> %s)"
 *                (boollist_to_string fv) (D.layout_label label))
 *         | None -> Hashtbl.add env.fvtab fv D.Pos
 *       in
 *       loop ()
 *   in
 *   loop () *)

let weaker_safe_loop ctx vc_env env =
  let rec loop () =
    let dt_spec, dt_idx =
      if Hashtbl.length env.fvtab == 0
      then D.T, D.T
      else D.classify_hash env.fset env.fvtab in
    let learned_body = Epr.simplify_ite @@ D.to_epr dt_spec in
    let new_spec = body_to_spec env learned_body in
    let new_sr = {env.current with additional_dt = dt_idx; additional_spec = new_spec} in
    (* let _ = Printf.printf "learn_weaker:\n%s\n" (Ast.layout_spec new_spec) in *)
    match neg_query ctx vc_env env new_sr with
    | Pass ->
      let new_spectable = StrMap.update env.hole.name
          (fun v -> match v with
             | None -> raise @@ InterExn "never happen multi_apply_constraint"
             | Some _ -> Some (get_increamental_spec new_sr))
          vc_env.spectable in
      {vc_env with spectable = new_spectable;},
      {env with current = new_sr;}
    | NeedRefine ->
      loop ()
  in
  loop ()

let refresh_single_abd_env env =
  let _ = Hashtbl.filter_map_inplace (fun _ label ->
      match label with
      | D.Pos -> Some D.Pos
      | D.Neg -> Some D.MayNeg
      | D.MayNeg -> Some D.MayNeg
    ) env.fvtab in
  ()

let update_vc_env vc_env spec_env =
  let new_spectable = StrMap.update spec_env.hole.name
      (fun v -> match v with
         | None -> raise @@ InterExn "refresh_vc_env"
         | Some _ -> Some (get_increamental_spec spec_env.current))
      vc_env.spectable in
  {vc_env with spectable = new_spectable}

let infer ctx vc_env env =
  let _ = Printf.printf "single infer: %s\n" (env.hole.name) in
  let _ = Printf.printf "env.fset: %s\n" (F.layout_set env.fset) in
  let max_loop_counter = ref 0 in
  let rec max_loop vc_env env =
    let rec find_pos env =
      match pos_query ctx vc_env env with
      | None -> None
      | Some fv ->
        let if_pos = pos_verify_update_env ctx vc_env env fv in
        if not if_pos then find_pos env else Some env
    in
    match find_pos env with
    | None ->
      if !max_loop_counter == 0 then None else Some (vc_env, env)
    | Some env ->
      let _ = max_loop_counter := !max_loop_counter + 1 in
      let vc_env, env = weaker_safe_loop ctx vc_env env in
      (* let _ = Printf.printf "new current:\n%s\n" (Ast.layout_spec env.current) in *)
      max_loop vc_env env
  in
  let env_opt = max_loop vc_env env in
  let _ = match env_opt with
    | None ->
      let _ = summary_fv_num env in
      Printf.printf "maxed\n"
    | Some (_, env) ->
      let _ = Printf.printf "max spec:\n%s\n" (Ast.layout_spec
                                                 (get_increamental_spec env.current)) in
      summary_fv_num env
  in
  env_opt

