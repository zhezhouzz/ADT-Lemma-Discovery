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

let init_unknown_fv fset =
  List.init (List.length fset) (fun i -> T.Bool, Printf.sprintf "_fv!%i" i)

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

let make_spec_with_unknown env =
  let fv_epr = unknown_fv_fset_to_epr env.fset env.unknown_fv in
  let _, (_, body) = env.current in
  let spec = env.hole.args,
             (env.qv,
              Epr.And [Epr.Or [body; fv_epr];]) in
  spec

let make_spec_with_fv env fv =
  let fv_epr = Epr.And (List.map (fun (f, b) ->
      if b then F.to_epr f else Epr.Not (F.to_epr f)
    ) (List.combine env.fset fv)) in
  let _, (_, body) = env.current in
  let spec = env.hole.args,
             (env.qv,
              Epr.And [Epr.Or [body; fv_epr];]) in
  spec

let fv_not_in_curr_constraint env =
  let args_e = List.map (fun v -> Epr.Atom (SE.from_tpedvar v)) env.unknown_fv in
  let body = D.to_epr_idx env.cur_dt args_e in
  Epr.Not body

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

let pos_query ctx env =
  let spec = make_spec_with_unknown env in
  let new_spectable = StrMap.update env.hole.name
      (fun v -> match v with
         | None -> raise @@ InterExn "never happen multi_apply_constraint"
         | Some _ -> Some spec)
      env.spectable in
  let pos_phi = Ast.to_z3 ctx (Ast.Implies (env.pre, env.post)) new_spectable in
  let force_enum_neg = Epr.to_z3 ctx
      (fv_not_in_curr_constraint env) in
  let force_no_repeat = Epr.to_z3 ctx @@ fv_no_repeat env in
  let pos_query = Boolean.mk_and ctx [pos_phi; force_enum_neg; force_no_repeat] in
  let _ = Printf.printf "pos_query:\n%s\n" (Expr.to_string pos_query) in
  let _, m = S.check ctx pos_query in
  match m with
  | None -> None
  | Some m ->
    let fv = S.get_unknown_fv ctx m env.unknown_fv in
    let _ = Printf.printf "fv = %s\n" (boollist_to_string fv) in
    Some fv

open Printf

type smt_status = Pass | NeedRefine

let gather_neg_fvec_to_tab_multi ctx env qvrange model =
    let se_range = List.map (fun x -> SE.Literal (T.Int, SE.L.Int x)) qvrange in
    let sub_assignment = List.map (fun _ -> se_range) env.qv in
    let _, names = List.split (env.hole.args @ env.qv) in
    let _ =
      List.map (fun args ->
          let args = List.map SE.from_tpedvar args in
          let extract_fvec _ values =
            let vec = List.map
                (fun feature ->
                   Epr.subst (F.to_epr feature) names (args @ values)) env.fset in
            let _ = printf "[vec]:%s\n" (List.to_string Epr.layout vec) in
            let vec' = List.map (fun e -> S.get_pred model (Epr.to_z3 ctx e)) vec in
            let _ = printf "[vec]:%s%s\n" (List.to_string Epr.layout vec)
                (boollist_to_string vec') in
            match Hashtbl.find_opt env.fvtab vec' with
            | Some Neg -> raise @@ InterExn "never happen single gather"
            | Some Pos | Some MayNeg -> ()
            | None ->
              if D.exec_vector_idx env.cur_dt vec'
              then Hashtbl.add env.fvtab vec' Pos
              else Hashtbl.add env.fvtab vec' MayNeg
          in
          let _ = List.choose_list_list_order_fold extract_fvec () sub_assignment in
          ()
        ) env.applied_args in
    ()

let pos_verify_update_env ctx env fv =
  let spec = make_spec_with_fv env fv in
  let new_spectable = StrMap.update env.hole.name
      (fun v -> match v with
         | None -> raise @@ InterExn "never happen multi_apply_constraint"
         | Some _ -> Some spec)
      env.spectable in
  let neg_phi = Ast.to_z3 ctx (Ast.Not (Ast.Implies (env.pre, env.post))) new_spectable in
  let _ = Printf.printf "verify:%s\n" (Expr.to_string neg_phi) in
  let if_pos, _ = S.check ctx neg_phi in
  let _ =
    if if_pos
    then Printf.printf "real pos[%s]\n" (boollist_to_string fv)
    else Printf.printf "false pos[%s]\n" (boollist_to_string fv)
  in
  let _ =
    match Hashtbl.find_opt env.fvtab fv, if_pos with
    | Some Pos, _ | Some Neg, _ | Some MayNeg, true
      -> raise @@ InterExn "never happen in single abduction"
    | Some MayNeg, false | None, false ->
      Hashtbl.replace env.fvtab fv Neg
    | None, true ->
      Hashtbl.add env.fvtab fv Pos
  in
  ()

let get_preds_interp model =
  let funcs = Model.get_func_decls model in
  let get func =
    match Model.get_func_interp model func with
    | None -> raise @@ InterExn "never happen"
    | Some interp ->
      let bounds =
        List.fold_left (fun l e ->
            Model.FuncInterp.FuncEntry.(
              List.map (fun bound ->
                  if Arithmetic.is_int_numeral bound
                  then int_of_string @@ Arithmetic.Integer.numeral_to_string bound
                  else raise @@ InterExn "bad bound"
                ) (get_args e)
            ) @ l
          ) [] (Model.FuncInterp.get_entries interp) in
      let bounds = List.remove_duplicates_eq bounds in
      (* let _ = printf "%s\n" (IntList.to_string bounds) in *)
      bounds
  in
  let bounds = List.remove_duplicates_eq @@ List.flatten @@ List.map get funcs in
  match IntList.max_opt bounds with
  | None -> [0]
  | Some ma -> (ma + 1) :: bounds

let body_to_spec env body =
  env.hole.args, (env.qv, body)

let neg_query ctx env new_spec =
  let counter = ref 0 in
  let rec loop (new_spec, _) =
    let new_spectable = StrMap.update env.hole.name
        (fun v -> match v with
           | None -> raise @@ InterExn "never happen multi_apply_constraint"
           | Some _ -> Some new_spec)
        env.spectable in
    let neg_phi = Ast.to_z3 ctx (Ast.Not (Ast.Implies (env.pre, env.post))) new_spectable in
    let _, m = S.check ctx neg_phi in
    match m with
    | None ->
      if !counter == 0 then Pass else NeedRefine
    | Some m ->
      let _ = Printf.printf "%s\n" (Model.to_string m) in
      let bounds = get_preds_interp m in
      let _ = gather_neg_fvec_to_tab_multi ctx env bounds m in
      let _ = Hashtbl.iter (fun vec label ->
          printf "%s:%s\n" (boollist_to_string vec) (D.layout_label label)
        ) env.fvtab in
      let dt, dt_idx =
        if Hashtbl.length env.fvtab == 0
        then D.T, D.T
        else D.classify_hash env.fset env.fvtab in
      let learned = body_to_spec env @@ Epr.simplify_ite @@ D.to_epr dt in
      let _ = counter := !counter + 1 in
      loop (learned, dt_idx)
  in
  loop new_spec

let learn_weaker ctx env =
  let current = StrMap.find "never happen learn_weaker"
      env.spectable env.hole.name in
  let _, (_, cur_body) = current in
  let fset_z3 = List.map (fun f -> Epr.to_z3 ctx @@ F.to_epr f) env.fset in
  let rec loop () =
    let dt, dt_idx =
      if Hashtbl.length env.fvtab == 0
      then D.T, D.T
      else D.classify_hash env.fset env.fvtab in
    let learned_body = Epr.simplify_ite @@ D.to_epr dt in
    let query = Epr.to_z3 ctx @@ Epr.Not (Epr.Implies (cur_body, learned_body)) in
    let if_weaker, m = S.check ctx query in
    if if_weaker
    then body_to_spec env learned_body, dt_idx
    else
      match m with
      | None -> raise @@ InterExn "never happen in learn_weaker(timeout)"
      | Some m ->
        let fv = List.map (fun feature -> S.get_pred m feature) fset_z3 in
        let _ =
          match Hashtbl.find_opt env.fvtab fv with
          | Some label -> raise @@ InterExn
              (sprintf "learn_weaker(exists %s -> %s)"
                 (boollist_to_string fv) (D.layout_label label))
          | None -> Hashtbl.add env.fvtab fv Pos
        in
        loop ()
  in
  loop ()

let weaker_safe_loop ctx env =
  let rec loop () =
    let new_spec, dt = learn_weaker ctx env in
    let _ = Printf.printf "learn_weaker:\n%s\n" (Ast.layout_spec new_spec) in
    match neg_query ctx env (new_spec, dt) with
    | Pass ->
      let new_spectable = StrMap.update env.hole.name
          (fun v -> match v with
             | None -> raise @@ InterExn "never happen multi_apply_constraint"
             | Some _ -> Some new_spec)
          env.spectable in
      {env with spectable = new_spectable; current = new_spec; cur_dt = dt}
    | NeedRefine ->
      loop ()
  in
  loop ()

let test_make_dt fset =
  let tab = Hashtbl.create 4 in
  let _ = Hashtbl.add tab [true;true] D.Neg in
  let _ = Hashtbl.add tab [true;false] D.Neg in
  let _ = Hashtbl.add tab [false;true] D.Neg in
  let _ = Hashtbl.add tab [false;false] D.Pos in
  let _, dt = D.classify_hash fset tab in
  dt

let test ctx preds bpreds pre post qv spectable hole_name hole_args =
  let hole = {name = hole_name; args = hole_args} in
  let fset = F.make_set_from_preds_multidt preds bpreds
      (hole.args @ qv) in
  let _ = Printf.printf "|Fset| = %i\n" (List.length fset) in
  let current = StrMap.find "miss current single abd"
      spectable hole.name in
  let env = {
    cur_dt = test_make_dt fset;
    current = current;
    qv = qv;
    fset = fset;
    pre = pre;
    post = post;
    spectable = spectable;
    hole = hole;
    applied_args = List.map (fun args ->
        List.map SE.to_tpedvar args
      ) (Ast.get_app_args pre hole.name);
    unknown_fv = init_unknown_fv fset;
    fvtab = Hashtbl.create 1000;
  }
  in
  let _ = Printf.printf "env.fset: %s\n" (F.layout_set env.fset) in
  let _ = List.iter (fun args ->
      Printf.printf "args: %s\n"
        (List.to_string T.layouttvar args)) env.applied_args in
  let phi = Ast.Implies (pre, post) in
  let _ = Printf.printf "phi:\n%s\n" (Ast.layout phi) in
  let rec max_loop env =
    match pos_query ctx env with
    | None -> env
    | Some fv ->
      let _ = pos_verify_update_env ctx env fv in
      let env = weaker_safe_loop ctx env in
      let _ = Printf.printf "new current:\n%s\n" (Ast.layout_spec env.current) in
      max_loop env
  in
  let env = max_loop env in
  let _ = Printf.printf "max spec:\n%s\n" (Ast.layout_spec env.current) in
  ()

