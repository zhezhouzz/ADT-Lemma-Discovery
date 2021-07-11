module SpecAbduction = struct
  module LH = Language.Helper
  module P = Pred.Pred
  module V = Pred.Value
  module Ast = Language.SpecAst
  module Epr = Ast.E
  module SE = Epr.SE
  module S = Solver
  module SZ = S.Z3aux
  module T = Tp.Tp
  module F = Feature.Feature
  module FV = Sample.FeatureVector
  module R = Randomgen.Randomgen
  module D = Dtree.Dtree

  open Utils
  open Printf
  open Z3
  open LH

  type label =
    | MultiPos
    | MultiMayNeg
    | MultiMayNegCache

  type spec_env = {
    dt: int D.t;
    qv: T.tpedvar list;
    fset: F.t list;
    (* applied_args: T.tpedvar list list; *)
    fvtab: (bool list, label) Hashtbl.t;
    abduciable: Epr.forallformula;
  }

  type multi_spec_env = {
    vc: Env.vc;
    spec_envs: spec_env StrMap.t;
    holes: hole StrMap.t;
    imps: (V.t list -> (V.t list option)) StrMap.t;
  }

  let is_pos = function
    | MultiPos -> true
    | _ -> false

  let sort_singles_by_fset l =
    let l' =
      List.sort (fun a b ->
          compare (List.length a.Env.fset) (List.length b.Env.fset)
        ) l
    in
    let _ = printf "sorted %s\n" @@ List.to_string (fun a -> a.Env.hole.name) l' in
    l'

  let loop_counter = ref 0

  let default_range = [2;3;4]
  let default_qv_range = 0 :: 1 :: default_range

  let samplebound = 4

  let singlenum = 4

  let get_inputs hole =
    let len = String.length hole.name in
    if len > 2 &&  Char.equal (String.get hole.name (len - 2)) '#'
    then
      if Char.equal (String.get hole.name (len - 1)) 't'
      then
        Some true, hole.args
      else
        Some false, hole.args
    else
      match hole.args with
      | [] -> raise @@ InterExn "never happen in get_inputs"
      | _ -> None, List.rev @@ List.tl @@ List.rev hole.args

  type sample_version = SV1 of int | SV2 of int
  let sver = ref (SV2 200)

  let handle_snum snum =
    match snum with None -> () | Some i -> sver := SV2 i

  let count_tested_sample env hole samples =
    let c = List.fold_left (fun c args_value ->
        let m = List.fold_left (fun m ((_, name), v) ->
            StrMap.add name v m
          ) StrMap.empty (List.combine hole.args args_value) in
        if Epr.forallformula_exec env.abduciable m
        then c
        else c + 1
      ) 0 samples in
    c

  let sampling hole imp env =
    let _, current_epr = env.abduciable in
    let _, inputs = get_inputs hole in
    (* let _ = printf "args = %s\n" (List.to_string T.layouttvar hole.args) in
     * let _ = printf "inputs = %s\n" (List.to_string T.layouttvar inputs) in *)
    let inputtps,_ = List.split inputs in
    let num = match !sver with SV1 num -> num | SV2 num -> num in
    let samples = R.gens ~chooses:default_range ~num:num
        ~tps:inputtps ~bound: samplebound in
    let samples = List.filter_map (fun input ->
        let output = imp input in
        match output with
        | Some output -> Some (input @ output)
        | None -> None
      ) samples in
    let c = count_tested_sample env hole samples in
    let s =
      match !sver with
      | SV1 _ ->
        let r = List.map (fun i -> V.I i) default_qv_range in
        let qvsamples = List.choose_list_list
            (List.map (fun _ -> r) env.qv) in
        List.cross samples qvsamples
      | SV2 _ ->
        let qvtypes, _ = List.split env.qv in
        let qvsamples =
          R.gens ~chooses:default_qv_range ~num:(List.length samples)
            ~tps:qvtypes ~bound: samplebound in
        List.combine samples qvsamples
    in
    (* let _ = List.iter (fun (s1,s2) -> printf "{%s},{%s}]\n"
     *                       (List.to_string V.layout s1)
     *                       (List.to_string V.layout s2)) s in *)
    let extract_fv (args_value, qv_value) =
      (* let _ = printf "{%s},{%s}]\n"
       *     (List.to_string V.layout args_value)
       *     (List.to_string V.layout qv_value) in
       * let _ = printf "{%s},{%s}]\n"
       *     (List.to_string T.layouttvar hole.args)
       *     (List.to_string T.layouttvar env.qv) in *)
      let m = StrMap.empty in
      let m = List.fold_left (fun m ((_, name), v) ->
          StrMap.add name v m
        ) m (List.combine hole.args args_value) in
      let m = List.fold_left (fun m ((_, name), v) ->
          StrMap.add name v m
        ) m (List.combine env.qv qv_value) in
      if Epr.exec current_epr m
      then None
      else
        let fv = (List.map (fun feature -> F.exec feature m) env.fset) in
        (* let _ =
         *   if List.eq (fun x y -> x == y) fv [false;false;true;false;false;false;false;false;false;true;true;false;true;false;false;true;true;false;false;false;true] then
         *     let _ =
         *       List.iter (fun (feature, value) ->
         *           printf "feature:%s --> %b\n" (F.layout feature) value
         *         ) (List.combine env.fset fv)
         *     in
         *     let _ = raise @@ InterExn "bad pos" in
         *     ()
         *   else
         *     ()
         * in *)
        (* let _  = printf "add pos %s\n" (boollist_to_string fv) in *)
        Some fv
    in
    let fvs = List.filter_map extract_fv s in
    let counter = ref 0 in
    let _ = List.iter (fun fv ->
        match Hashtbl.find_opt env.fvtab fv with
        | Some MultiPos -> ()
        | Some MultiMayNegCache -> raise @@ InterExn "never happen sampling"
        | Some MultiMayNeg ->
          let _ = counter := !counter + 1 in
          (* let _ = printf "add pos %s\n" (boollist_to_string fv) in *)
          Hashtbl.replace env.fvtab fv MultiPos
        | None ->
          let _ = counter := !counter + 1 in
          (* let _ = printf "add pos %s\n" (boollist_to_string fv) in *)
          Hashtbl.add env.fvtab fv MultiPos
      ) fvs in
    let _ = printf "sampling [%s] len(fvs) = %i\n" hole.name (!counter) in
    c, List.length fvs

  let gather_neg_fvec_to_tab ctx hole env applied_args qvrange model query =
    let se_range = List.map (fun x -> SE.Literal (T.Int, SE.L.Int x)) qvrange in
    let sub_assignment = List.map (fun _ -> se_range) env.qv in
    let _, names = List.split (hole.args @ env.qv) in
    let counter = ref 0 in
    let _ =
      List.map (fun args ->
          (* let args = List.map SE.from_tpedvar args in *)
          (* let _ = printf "args:%s\n" (List.to_string SE.layout args) in *)
          let extract_fvec _ values =
            (* let _ = printf "names: %s\n" (List.to_string (fun x -> x) names) in *)
            (* let _ = printf "vs: %s\n" (List.to_string SE.layout (args @ values)) in *)
            let vec = List.map
                (fun feature ->
                   Epr.subst (F.to_epr feature) names (args @ values)) env.fset in
            let vec' = List.map (fun e -> S.get_pred model (Epr.to_z3 ctx e)) vec in
            (* let _ = printf "[vec]:%s%s\n" (List.to_string Epr.layout vec)
             *     (boollist_to_string vec') in *)
            match Hashtbl.find_opt env.fvtab vec' with
            | Some MultiMayNeg ->
              let _ = printf "%s\n" (Expr.to_string query) in
              let _ = printf "[vec]:%s%s\n" (List.to_string Epr.layout vec)
                  (boollist_to_string vec') in
              raise @@ InterExn "never happen gather_neg_fvec_to_tab"
            | Some MultiPos ->
              (* let _ = printf "[vec]:%s%s\n" (List.to_string Epr.layout vec)
               *     (boollist_to_string vec') in *)
              (* let _ = printf "pos:%s\n"  (boollist_to_string vec') in *)
              ()
            | Some MultiMayNegCache ->
              let _ = counter := !counter + 1 in
              (* let _ = printf "may neg cache:%s\n"  (boollist_to_string vec') in *)
              ()
            | None ->
              let _ = counter := !counter + 1 in
              (* let _ = printf "neg:%s\n"  (boollist_to_string vec') in *)
              Hashtbl.add env.fvtab vec' MultiMayNegCache
          in
          let _ = List.choose_list_list_order_fold extract_fvec () sub_assignment in
          ()
        ) applied_args in
    !counter

  let name_qv qv_num = List.map (fun n -> (T.Int, n)) @@ List.init qv_num (fun i -> sprintf "u_%i" i)

  let init_spec_env hole preds numX =
    let qv = name_qv numX in
    let fset = F.make_set_from_preds_max preds hole.args qv in
    let _ = printf "init-set:%s\n" (F.layout_set fset) in
    let fvtab = Hashtbl.create 10000 in
    let abduciable = [], Epr.Not Epr.True in
    {dt = D.F;
     qv = qv;
     fset = fset;
     fvtab = fvtab;
     abduciable = abduciable;}

  type multi_infer_input = {
    upost: Ast.t;
    uvars: T.tpedvar list;
    uinputs: T.tpedvar list;
    uoutputs: T.tpedvar list;
    uprog: V.t list -> (V.t list) option;
  }

  let init_env mii pre spectable preds numX holel =
    let holes, imps = List.fold_left (fun (m, imp_m) (hole, imp) ->
        (StrMap.add hole.name hole m,
         StrMap.add hole.name imp imp_m)
      ) (StrMap.empty, StrMap.empty) holel in
    let multi_pre =
      List.map (fun pre ->
          let applied_args_map = StrMap.mapi (fun name _ ->
             Ast.get_app_args pre name
            ) holes in
          let applied_args_map = StrMap.filter (fun _ r ->
              match r with
              | [] -> false
              | _ -> true
            ) applied_args_map in
          {Env.pre_flow = pre; Env.applied_args_map = applied_args_map}
        ) pre in
    let spec_envs = StrMap.map (fun hole ->
        init_spec_env hole preds numX
      ) holes in
    let spectable = StrMap.fold (fun specname spec_env m ->
        let hole = StrMap.find "init_env" holes specname in
        StrMap.update specname (fun spec ->
            match spec with
            | None -> Some (hole.args, spec_env.abduciable)
            | Some _ -> raise @@ InterExn "init_env"
          ) m
      ) spec_envs spectable
    in
    let vc = {
      Env.preds = preds;
      Env.vars = mii.uvars;
      Env.inputs = mii.uinputs;
      Env.outputs = mii.uoutputs;
      Env.prog = mii.uprog;
      Env.multi_pre =  multi_pre;
      Env.post = mii.upost;
      Env.spectable = spectable;
    } in
    { vc = vc;
      holes = holes;
      imps = imps;
      spec_envs = spec_envs;
    }

  let learn_in_spec_env env =
    let dt, dtidx =
      if Hashtbl.length env.fvtab == 0
      then D.T, D.T
      else D.classify_hash env.fset env.fvtab is_pos in
    let abduciable = D.to_epr dt in
    let abduciable = Epr.simplify_dt_result abduciable in
    (* let _ = printf "\traw abduciable:\n%s\n" (Epr.pretty_layout_epr abduciable) in *)
    let abduciable = env.qv, abduciable in
    {env with abduciable = abduciable; dt = dtidx}

  let inplace_gather_fv ctx model query qvrange env flow stat_once =
    let total_neg_num = ref 0 in
    let _ = StrMap.iter
        (fun specname applied_args ->
           let hole = StrMap.find "update_spec_env" env.holes specname in
           let spec_env = StrMap.find "update_spec_env" env.spec_envs specname in
           let neg_num =
             gather_neg_fvec_to_tab ctx hole spec_env applied_args qvrange model query
           in
           let _ = printf "[%s] neg_num:%i\n" hole.name neg_num in
           let _ = total_neg_num := !total_neg_num + neg_num in
           ()
        ) flow.Env.applied_args_map in
    let _ = printf "total_neg_num:%i\n" (!total_neg_num) in
    let _ = stat_once.Env.num_fv_of_cex := !(stat_once.Env.num_fv_of_cex) + !total_neg_num in
    if !total_neg_num == 0 then Some flow.pre_flow else None

  let update_env_spectable env =
    let spectable' = StrMap.fold (fun specname spec_env spectable ->
        let hole = StrMap.find "update_env" env.holes specname in
        StrMap.update specname (fun spec ->
            match spec with
            | None -> raise @@ InterExn "update_env"
            | Some _ -> Some (hole.args, spec_env.abduciable)
          )  spectable
      ) env.spec_envs env.vc.Env.spectable in
    {env with vc = {env.vc with Env.spectable = spectable'}}

  type neg_result =
    | Verified
    | CannotGather
    | Gathered
    | RealCex of (V.t StrMap.t) list

  let is_verified = function
    | Verified -> true
    | _ -> false
  let is_cannot_gather = function
    | CannotGather -> true
    | _ -> false
  let is_real_cex = function
    | RealCex _ -> true
    | _ -> false

  let model_to_instance ctx vc model version =
    let _ = printf "%s\n" (Model.to_string model) in
    let qvrange = S.Z3aux.get_preds_interp model version in
    let handle_input (tp, name) pred =
      let dtse = SE.from_tpedvar (tp, name) in
      let info = P.find_pred_info_by_name pred in
      let args = List.map (List.map (fun i -> SE.Literal (T.Int, SE.L.Int i))) @@
          List.choose_n qvrange info.P.num_int in
      let atoms = List.map (fun args ->
          Epr.Atom (SE.Op (T.Bool, pred, dtse :: args))) args in
      let constr = Epr.And (List.map (fun e ->
          let b = S.get_pred model (Epr.to_z3 ctx e) in
          if b then e else Epr.Not e
        ) atoms) in
      let _ = printf "constr:%s\n" (Epr.pretty_layout_epr constr) in
      constr
    in
    let handle_input x = Epr.And (List.map (handle_input x) vc.Env.preds) in
    let inputs_instances = List.map (fun (tp, name) ->
        match tp with
        | T.Bool -> [V.B (S.get_pred model (S.Z3aux.tpedvar_to_z3 ctx (tp, name)))]
        | T.Int -> [V.I (S.get_int_name ctx model name)]
        | _ ->
          let c = handle_input (tp, name) in
          let samples = R.gen_one ~chooses:qvrange ~num:50
              ~tp:tp ~bound:samplebound in
          let makem v = StrMap.add name v StrMap.empty in
          (* let _ = List.iter (fun v ->
           *     printf "raw: %s;\n" (V.layout v)
           *   ) samples in
           * let _ = printf "\n" in *)
          let samples = List.filter_map (fun v ->
              if Epr.exec c (makem v) then Some v else None
            ) samples in
          (* let _ = List.iter (fun v ->
           *     printf "instance: %s;\n" (V.layout v)
           *   ) samples in
           * let _ = printf "\n" in *)
          samples
      ) vc.inputs in
    let inputs_instances = List.choose_list_list @@
      List.map (List.remove_duplicates V.eq) inputs_instances in
    let ms = List.filter_map (fun vs ->
        match vc.prog vs with
        | None -> None
        | Some outputs ->
          let m = StrMap.empty in
          let m = List.fold_left (fun m ((_, name), v) ->
              StrMap.add name v m
            ) m (List.combine vc.inputs vs) in
          let m = List.fold_left (fun m ((_, name), v) ->
              StrMap.add name v m
            ) m (List.combine vc.outputs outputs) in
          (* let _ = StrMap.iter (fun name v ->
           *     printf "%s -> %s; " name (V.layout v)
           *   ) m in
           * let _ = printf "\n" in *)
          if Ast.exec vc.post vc.spectable m
          then None
          else Some m
      ) inputs_instances in
    (* let _ = List.iter (fun m -> StrMap.iter (fun name v ->
     *     printf "%s -> %s" name (V.layout v)
     *   ) m) ms in *)
    ms

  let inplace_verify_and_gather_fv ctx env flow stat_once =
    let handle_model smt_query model version =
      let _ = addadd stat_once.Env.num_cex in
      let qvrange = S.Z3aux.get_preds_interp model version in
      (match inplace_gather_fv ctx model smt_query qvrange env flow stat_once with
       | None -> Gathered
       | Some pre ->
         (* let _ = printf "smt_query\n%s\n" (Expr.to_string smt_query) in
          * let _ = printf "model:\n%s\n" (Model.to_string model) in
          * let _ = printf "flow:\n%s\n" (Ast.vc_layout flow.Env.pre_flow) in
          * let _ = model_to_instance ctx env.vc model version in
          * let _ = raise @@ InterExn "inplace_verify_and_gather_fv end" in *)
         let ms = model_to_instance ctx env.vc model version in
         if List.length ms == 0 then
           (printf "cannot gather fv in ast:%s\n" (Ast.vc_layout pre);
            CannotGather)
         else
           (RealCex ms)
      )
    in
    (* let _ = printf "post:%s\n" (Ast.layout env.vc.Env.post) in *)
    let build_smt_query version =
      Ast.to_z3 ctx
        (Ast.Not (Ast.Implies (flow.Env.pre_flow, env.vc.Env.post)))
        env.vc.Env.spectable version env.vc.Env.vars
    in
    let version = S.Z3aux.V1 in
    let smt_query = build_smt_query version in
      match S.check ctx smt_query with
      | S.SmtUnsat -> Verified
        (* let version = S.Z3aux.V2 in
         * let smt_query = build_smt_query version in
         * (match S.check ctx smt_query with
         *  | S.SmtUnsat -> Verified
         *  | S.Timeout ->
         *    let _ = printf "%s\n" (Expr.to_string smt_query) in
         *    raise (InterExn "multi inference time out!")
         *  | S.SmtSat model -> handle_model smt_query model version) *)
      | S.Timeout ->
        raise @@ InterExn (Printf.sprintf "[%s]inplace_verify_and_gather_fv time out!" (SZ.layout_imp_version version))
      | S.SmtSat model -> handle_model smt_query model version

  let negcache_to_neg env =
    StrMap.iter (fun _ spec_env ->
        Hashtbl.filter_map_inplace (fun _ label ->
            match label with
            | MultiPos -> Some MultiPos
            | MultiMayNeg | MultiMayNegCache -> Some MultiMayNeg
          ) spec_env.fvtab
      ) env.spec_envs

  type neg_refine_result =
    | NRFCex of (V.t StrMap.t) list
    | NRFIncreaseHyp
    | NRFNewEnv of multi_spec_env

  type pos_refine_result =
    | PRFCex of (V.t StrMap.t) list
    | PRFIncreaseHyp
    | PRFFinalEnv of multi_spec_env

  let refinement_loop ctx env cstat_once =
    let _ = printf "refinement_loop\n" in
    let rec neg_refine_loop env =
      (* let _ = printf "neg loop\n" in *)
      let _ = loop_counter := !loop_counter + 1 in
      (* let (fvs, res) = List.fold_left (fun (fvs, res) flow ->
       *     let (fvs, r) = inplace_verify_and_gather_fv ctx env flow fvs in
       *     fvs, res @ [r]
       *   ) (Hashtbl.create 1000, []) env.vc.Env.multi_pre in *)
      let res = List.map (fun flow ->
          inplace_verify_and_gather_fv ctx env flow cstat_once
        ) env.vc.Env.multi_pre in
      if List.for_all is_verified res
      then NRFNewEnv env
      else if List.exists is_real_cex res
      then
        let cexs = List.find_all is_real_cex res in
        let cexs = List.flatten @@ List.map (fun res ->
            match res with
            | RealCex ms -> ms
            | _ -> raise @@ InterExn "refinement_loop"
          ) cexs in
        NRFCex cexs
      else if List.exists is_cannot_gather res
      then NRFIncreaseHyp
      else
        let _ = negcache_to_neg env in
        let spec_envs' = StrMap.map learn_in_spec_env env.spec_envs in
        let env = {env with spec_envs = spec_envs'} in
        let env = update_env_spectable env in
        neg_refine_loop env
    in
    let rec pos_refine_loop env =
      let _ = addadd cstat_once.Env.num_pos_refine in
      let total_pos_num = ref 0 in
      let total_sample_pos_num = ref 0 in
      let spec_envs' = StrMap.mapi (fun specname spec_env ->
          let hole = StrMap.find "pos_refine_loop" env.holes specname in
          let imp = StrMap.find "pos_refine_loop" env.imps specname in
          let pos_sample_num, pos_num = sampling hole imp spec_env in
          let _ = total_pos_num := !total_pos_num + pos_num in
          let _ = total_sample_pos_num := !total_sample_pos_num + pos_sample_num in
          let spec_env = learn_in_spec_env spec_env in
          spec_env
        ) env.spec_envs
      in
      let _ = cstat_once.Env.num_fv_of_samples :=
          !total_pos_num + !(cstat_once.Env.num_fv_of_samples) in
      let _ = cstat_once.Env.num_pos_sample_violate_spec :=
          !total_sample_pos_num + !(cstat_once.Env.num_pos_sample_violate_spec) in
      if !total_pos_num > 0
      then
        let env = {env with spec_envs = spec_envs'} in
        let env = update_env_spectable env in
        let res = neg_refine_loop env in
        match res with
        | NRFCex cexs -> PRFCex cexs
        | NRFNewEnv env -> pos_refine_loop env
        | NRFIncreaseHyp -> PRFIncreaseHyp
      else
        PRFFinalEnv env
    in
    pos_refine_loop env

  let init_unknown_fv fset =
    List.init (List.length fset) (fun i -> T.Bool, Printf.sprintf "_fv!%i" i)

  let make_single_abd_env vc_env spec_env hole preds uniform_qv_num =
    let qv = name_qv uniform_qv_num in
    let fset = F.make_set_from_preds_max preds hole.args qv in
    let _ = if List.length spec_env.qv > List.length qv then
        raise @@ InterExn "not impelemented make_single_abd_env" else ()
    in
    let _ = Printf.printf "|Fset| = %i\n" (List.length fset) in
    let args, (_, body) = StrMap.find "miss current single abd"
        vc_env.Env.spectable hole.name in
    let m = List.fold_lefti (fun m i f ->
        let i' = List.find_index "make_single_abd_env" (fun f' -> F.eq f f') fset in
        IntMap.add i i' m
      ) IntMap.empty spec_env.fset in
    let spec = args, (qv, body) in
    let dt = D.map m spec_env.dt in
    let fvtab' = Hashtbl.create 10000 in
    let current =
      if List.length spec_env.qv == List.length qv then
        let _ = Hashtbl.iter (fun vec label ->
        match label with
          | MultiPos -> Hashtbl.add fvtab' vec D.Pos
          | MultiMayNeg -> Hashtbl.add fvtab' vec D.MayNeg
          | MultiMayNegCache -> raise @@ InterExn "never happen in make_single_abd_env"
          ) spec_env.fvtab in
        {Env.init_spec = spec;
         Env.init_dt = dt;
         Env.additional_spec = spec;
         Env.additional_dt = dt;
        }
      else
        {Env.init_spec = spec;
         Env.init_dt = dt;
         Env.additional_spec = hole.args, (spec_env.qv, Epr.(Not True));
         Env.additional_dt = D.F
        }
    in
    let single_env = {
      Env.current = current;
      Env.qv = qv;
      Env.fset = fset;
      Env.hole = hole;
      Env.unknown_fv = init_unknown_fv fset;
      Env.fvtab = fvtab';
      Env.if_maximal = false
    }
    in
    single_env

  let rec pow a = function
    | 0 -> 1
    | 1 -> a
    | n ->
      let b = pow a (n / 2) in
      b * b * (if n mod 2 = 0 then 1 else a)

  type consistent_result =
    | CRCex of (V.t StrMap.t) list
    | CRFinalEnv of multi_spec_env

  let max_qv = 4

  let consistent_solution ctx benchname mii pres spectable holel preds startX =
    let cstat = Env.init_consistent_stat () in
    let rec search_hyp numX =
      let _ = if numX >= max_qv then
          let _ = Env.save_consistent_stat benchname cstat in
          raise @@ InterExn "Cannot find consistent solutoin. The client code is wrong but cannot find concrete Cex."
        else () in
      let env = init_env mii pres spectable preds numX holel in
      let _ = StrMap.iter (fun name env ->
          printf "[%s] space: 2^%i = %i\n"
            name (List.length env.fset) (pow 2 (List.length env.fset))
        ) env.spec_envs in
      let stat_once = Env.init_consistent_stat_once numX in
      let result, delta_time = time (fun _ -> refinement_loop ctx env stat_once) in
      let _ = stat_once.run_time := delta_time in
      let _ = cstat.Env.consist_list := !(cstat.Env.consist_list) @ [stat_once] in
      match result with
      | PRFIncreaseHyp -> search_hyp (numX + 1)
      | PRFFinalEnv spec -> CRFinalEnv spec
      | PRFCex cexs -> CRCex cexs
    in
    let result = search_hyp startX in
    let _ = Env.save_consistent_stat benchname cstat in
    result

  let merge_current sr fset =
    let spec, dt = D.merge_dt fset sr.Env.init_dt sr.Env.additional_dt in
    (* let spec, dt = D.subtract_dt fset sr.Env.additional_dt sr.Env.init_dt in *)
    spec, dt

  let merge_envs total_env single_envs_arr =
    Array.fold_left (fun total_env single_env ->
        let spec, _ = merge_current single_env.Env.current single_env.Env.fset in
        let abduciable = D.to_epr spec in
        let abduciable = Epr.simplify_dt_result abduciable in
        let spec = single_env.hole.args, (single_env.qv, abduciable) in
        let _ = printf "merged [%s]:\n%s\n"
            single_env.hole.name (Ast.layout_spec spec) in
        let new_spectable = StrMap.update single_env.Env.hole.name
            (fun v -> match v with
               | None -> raise @@ InterExn "merge_envs"
               | Some _ -> Some spec)
            total_env.Env.spectable in
        {total_env with Env.spectable = new_spectable}
      ) total_env single_envs_arr

  let epr_exec_fv epr fset fv =
    let equlity_extract m =
      Hashtbl.fold (fun epr b l ->
          match epr, b with
          | Epr.Atom (SE.Op (_, op, [x;y])), true when String.equal op "==" ->
            (x, y) :: l
          | _ -> l
        ) m []
    in
    let extend m (x, y) =
      let x, y =
        match x with
        | SE.Var (_, name) -> (name, y)
        | _ -> raise @@ InterExn "equlity_extract::extend"
      in
      let l = Hashtbl.fold (fun epr b l ->
          match epr with
          | Epr.Atom e -> (Epr.Atom (SE.subst e [x] [y]), b) :: l
          | _ -> raise @@ InterExn "equlity_extract::extend"
        ) m [] in
      let _ = List.iter (fun (epr, b) ->
          match Hashtbl.find_opt m epr with
          | Some _ -> ()
          | None -> Hashtbl.add m epr b
        ) l in
      ()
    in
    let m = Hashtbl.create 100 in
    (* let _ = printf "fset:%s\n" (F.layout_set fset) in *)
    let fset = List.map (fun fature -> F.to_epr fature) fset in
    let _ = List.iter (fun (f, b) -> Hashtbl.add m f b) (List.combine fset fv) in
    let _ = List.iter (fun (x, y) -> extend m (x, y)) (equlity_extract m) in
    (* let _ = printf "tab\n" in
     * let _ = Hashtbl.iter (fun epr b ->
     *     printf "[%s] -> %b\n" (Epr.layout epr) b
     *   ) m in *)
    let rec aux body =
      let open Epr in
      match body with
      | True -> true
      | Atom _ as feature ->
        (match Hashtbl.find_opt m feature with
         | None -> raise @@ InterExn (sprintf "spec_exec_fv:%s\n" (pretty_layout_epr feature))
         | Some b -> b
        )
      | Implies (p1, p2) ->
        if aux p1 then aux p2 else true
      | Ite (p1, p2, p3) ->
        if aux p1 then aux p2 else aux p3
      | Not body -> not (aux body)
      | And ps -> List.fold_left (fun r body ->
          if r then aux body else false
        ) true ps
      | Or ps -> List.fold_left (fun r body ->
          if r then true else aux body
        ) false ps
      | Iff (p1, p2) -> (aux p1) == (aux p2)
    in
    aux epr

  let operate_epr f fset epr1 epr2 =
    let len = List.length fset in
    let fv_arr = Array.init len (fun _ -> false) in
    let rec next idx =
      if idx >= len then None
      else if not (fv_arr.(idx)) then (Array.set fv_arr idx true; Some idx)
      else
        match next (idx + 1) with
        | None -> None
        | Some _ -> (Array.set fv_arr idx false; Some 0)
    in
    let size = pow 2 len in
    let ftab = Hashtbl.create size in
    let pos_counter = ref 0 in
    let rec aux idx =
      let fvec = Array.to_list fv_arr in
      (* let _ = Printf.printf "[%i]iter:%s\n" size (boollist_to_string fvec) in *)
      (* let _ = if !pos_counter > 100 then raise @@ InterExn "end" else () in *)
      let dt1_b = epr_exec_fv epr1 fset fvec in
      let dt2_b = epr_exec_fv epr2 fset fvec in
      let _ = if f dt1_b dt2_b then
          let _ = pos_counter := !pos_counter + 1 in
          Hashtbl.add ftab fvec D.Pos
        else
          Hashtbl.add ftab fvec D.Neg
      in
      match next idx with
      | None -> ()
      | Some idx -> aux idx
    in
    let _ = aux 0 in
    let result = Epr.simplify_dt_result @@
      D.to_epr @@
      fst @@ D.classify_hash fset ftab D.is_pos in
    !pos_counter, result

  let merge_spec spec preds =
    let (args, (qv, body)) = spec in
    let handle body_init body_add =
      let fset = F.make_set_from_preds_max preds args qv in
      let c, body = operate_epr (fun e1 e2 -> e1 || e2) fset body_init body_add in
      let spec' = (args, (qv, body)) in
      c, spec'
    in
    match body with
    | Epr.Or [body_init; body_add] -> handle body_init body_add
    | _ as body_init ->
      let c, _ = handle body_init (Epr.Not Epr.True) in
      c, spec

  let smt_merge_epr ctx preds args init addition =
    let init_qv, init_body = init in
    let addition_qv, addition_body = addition in
    (* let _ = printf "%s\n" (Epr.pretty_layout_forallformula init) in *)
    (* let _ = printf "%s\n" (Epr.pretty_layout_forallformula addition) in *)
    let fset = F.make_set_from_preds_max preds args addition_qv in
    (* let _ = printf "%s\n" (F.layout_set fset) in *)
    let fvtab = Hashtbl.create 10000 in
    (* let unknown_fv = List.init (List.length fset) (fun i -> T.Int, sprintf "fv!%i" i) in *)
    let fset_z3 = List.map (fun v -> Epr.to_z3 ctx @@ F.to_epr v) fset in
    let learn fvtab =
      (* let _ = Hashtbl.iter (fun vec label ->
       *     printf "[%s]%s\n" (boollist_to_string vec) (D.layout_label label)
       *   ) fvtab in *)
      let dt, dtidx =
        if Hashtbl.length fvtab == 0
        then D.T, D.T
        else D.classify_hash fset fvtab D.is_pos in
      let abduciable = D.to_epr dt in
      dt, dtidx, abduciable
    in
    let raw_init_body =
      match init_qv with
      | [] -> raise @@ InterExn "pos_gather"
      | [u] ->
      Epr.And (List.map (fun u' ->
        Epr.subst init_body [snd u] [SE.from_tpedvar u']
          ) addition_qv)
      | [_;_] -> init_body
      | _ -> raise @@ InterExn "pos_gather"
    in
    let gather posq fvtab =
      let (_, _, result) = learn fvtab in
      let q =
          (if posq
           then
             Epr.And [Epr.Or [raw_init_body; addition_body];
                      Epr.Not result;]
           else
             Epr.And [Epr.Not (Epr.Or [raw_init_body; addition_body]);
                      result;]
          )
      in
      (* let _ = printf "%b:\n%s\n" posq (Epr.pretty_layout_epr q) in *)
      let q = Epr.to_z3 ctx q in
      (* let _ = printf "%b:\n%s\n" posq (Expr.to_string q) in *)
      match S.check ctx q with
      | S.SmtUnsat ->
        (* let _ = printf "%b: unsat\n" posq in *)
        None
      | S.Timeout -> raise @@ InterExn "smt_merge_spec: timeout"
      | S.SmtSat m ->
        (* let _ = printf "%s\n" (Model.to_string m) in *)
        let fv = List.map (fun p -> S.get_pred m p) fset_z3 in
        Some fv
    in
    let neg_loop fvtab =
      let rec aux fvtab =
        match gather false fvtab with
        | Some fv ->
          let _ = Hashtbl.add fvtab fv D.Neg in
          let _ = aux fvtab in
          false, fvtab
        | None -> true, fvtab
      in
      aux fvtab
    in
    let pos_loop fvtab =
      let rec aux fvtab =
        match gather true fvtab with
        | Some fv ->
          let _ = Hashtbl.add fvtab fv D.Pos in
          let _ = aux fvtab in
          false, fvtab
        | None -> true, fvtab
      in
      aux fvtab
    in
    let rec aux fvtab =
      let if_already_pos, fvtab = neg_loop fvtab in
      let if_already_neg, fvtab = pos_loop fvtab in
      if if_already_pos && if_already_neg
      then fvtab
      else aux fvtab
    in
    let (_, dtidx, result) = learn (aux fvtab) in
    let c = D.count (List.length fset) dtidx in
    let p, n = Hashtbl.fold (fun _ label (p, n) ->
        match label with
        | D.Pos -> (p + 1, n)
        | _ -> (p, n + 1)
      ) fvtab (0, 0) in
    let _ = printf "p:%i n:%i\n" p n in
    c, (addition_qv, result)

  let smt_merge_spectable ctx consistentfilename resultfilename output =
    let (_, consistentresult) = Env.decode_infer_result
      @@ Yojson.Basic.from_file (consistentfilename) in
    let (preds, result) = Env.decode_infer_result
      @@ Yojson.Basic.from_file (resultfilename) in
    let cm = Hashtbl.create 10 in
    let m = StrMap.mapi (fun name (args, spec) ->
        match spec with
        | qv, Epr.Or [_; addition] ->
          let (_, init) = StrMap.find "smt_merge_spectable" consistentresult name in
          let c, result' = smt_merge_epr ctx preds args init (qv, addition) in
          let _ = Hashtbl.add cm name c in
          args, result'
        | _ -> raise @@ InterExn "smt_merge_spectable"
      ) result in
    let _ = Hashtbl.iter (fun name c ->
        printf "%s.#fev+: %i\n" name c
      ) cm
    in
    Yojson.Basic.to_file output (Env.encode_infer_result (preds, m))

  let merge_spectable spectable preds =
    StrMap.map (fun spec ->
        snd @@ merge_spec spec preds
      ) spectable

  let try_tmp tmpfile =
    let _, envs = Env.decode_weakening @@ Yojson.Basic.from_file tmpfile in
    let t_env = List.find "try_tmp" (fun env -> String.equal env.Env.hole.name "t") envs in
    let p, n = Hashtbl.fold (fun _ label (p, n) ->
        match label with
        | D.Pos -> (p + 1, n)
        | _ -> (p, n + 1)
      ) t_env.Env.fvtab (0, 0) in
    let _ = printf "p:%i n:%i\n" p n in
    let _, dtidx =
      if Hashtbl.length t_env.fvtab == 0
          then D.T, D.T
          else D.classify_hash t_env.fset t_env.fvtab D.is_pos in
    let c = D.count (List.length t_env.fset) dtidx in
    let _ = printf "count: %i\n" c in
    ()

  let merge_max_result _ resultfilename =
    let result = Yojson.Basic.from_file (resultfilename) in
    let (preds, result) = Env.decode_infer_result result in
    let _ = printf "before:\n" in
    let _ = StrMap.iter (fun name spec ->
        printf "%s\n" (Ast.layout_spec_entry name spec)
      ) result in
    let _ = printf "after:\n" in
    let merged = merge_spectable result preds in
    StrMap.iter (fun name spec ->
        let _ = printf "[size:%i]%s\n" (Ast.spec_num_atom spec)
            (Ast.layout_spec_entry name spec) in
        (* let (_, (_, body)) = spec in
         * let body_z3 = Epr.to_z3 ctx body in
         * let _ = printf "\n%s\n" (Expr.to_string body_z3) in
         * let body_z3' = Expr.simplify body_z3 None in
         * let _ = printf "\n%s\n" (Expr.to_string body_z3') in *)
        ()
      ) merged

  let verify_flow ctx vc flow =
    let build_smt_query version = Ast.to_z3 ctx
        (Ast.Not (Ast.Implies (flow.Env.pre_flow, vc.Env.post)))
        vc.Env.spectable version vc.Env.vars in
    let version = S.Z3aux.V2 in
    let smt_query = build_smt_query version in
    let _ = printf "%s\n" (Expr.to_string smt_query) in
    match S.check ctx smt_query with
    | S.SmtUnsat -> true
    | S.Timeout ->
      let _ = printf "%s\n" (Expr.to_string smt_query) in
      raise @@ InterExn (Printf.sprintf "[%s]verify_flow time out!" (SZ.layout_imp_version version))
    | S.SmtSat _ -> false

  let verify ctx vc =
    let res = List.map (fun flow -> verify_flow ctx vc flow) vc.Env.multi_pre in
    List.for_all (fun x -> x) res

  let spectable_filter_result names spectable =
    List.fold_left (fun m name ->
        let spec = StrMap.find "spectable_filter_result" spectable name in
        StrMap.add name spec m) StrMap.empty names

  let save_result name preds names vc =
    let result = spectable_filter_result names vc.Env.spectable in
    (* let _ = StrMap.iter (fun name spec ->
     *     printf "%s\n" (Ast.layout_spec_entry name spec)
     *   ) result in *)
    let _ = Yojson.Basic.to_file name
        (Env.encode_infer_result (preds, result)) in
    ()

  let time_bound = Some 3600.0
  (* let time_bound = None *)

  type mode = Bound | Oracle

  type multi_infer_result =
    | Cex of (V.t StrMap.t) list
    | Result of (Ast.spec StrMap.t)

  let weakening ctx benchname vc single_envs time_bound =
    let names = List.map (fun e -> e.Env.hole.name) single_envs in
    let single_envs_arr = Array.of_list single_envs in
    let mode = ref Bound in
    let rec aux total_env idx =
      if idx >= Array.length single_envs_arr
      then total_env
      else
        let single_env = single_envs_arr.(idx) in
        let time_bound = match !mode with
          | Oracle -> None
          | Bound -> time_bound
        in
        let (single_result, stat), delta_time =
          time (fun _ -> Single_abd.infer ctx benchname total_env single_env time_bound) in
        let _ = printf "time: single: %s: %fs\n" single_env.Env.hole.name delta_time in
        match single_result with
        | Env.AlreadyMaxed single_env' ->
          let _ = Array.set single_envs_arr idx single_env' in
          aux total_env (idx + 1)
        | Env.MayAlreadyMaxed single_env' ->
          let _ = Array.set single_envs_arr idx single_env' in
          aux total_env (idx + 1)
        | Env.NewMaxed (total_env, single_env') ->
          let _ = Array.set single_envs_arr idx single_env' in
          let _ = Env.save_stat benchname single_env'.hole.name time_bound stat in
          aux total_env (idx + 1)
        | Env.Weaker (total_env, single_env') ->
          let _ = Array.set single_envs_arr idx single_env' in
          let _ = Env.save_stat benchname single_env'.hole.name time_bound stat in
          aux total_env (idx + 1)
    in
    let total_env = aux vc 0 in
    let _ = save_result (benchname ^ "_bound_maximal.json") total_env.preds names total_env in
    let midfile = benchname ^ "_" ^ "bound.json" in
    let _ = Yojson.Basic.to_file midfile
        (Env.encode_weakening (total_env, Array.to_list single_envs_arr)) in
    (* let total_env', single_envs' = Env.decode_weakening @@ Yojson.Basic.from_file midfile in
     * let _ = printf "spectabeq: %b\n" (Ast.spectable_eq
     *                                     total_env.Env.spectable
     *                                     total_env'.Env.spectable) in
     * let _ = List.iter (fun (e, e') -> D.fvtab_eq e.Env.fvtab e'.Env.fvtab) @@
     *   List.combine (Array.to_list single_envs_arr) single_envs' in *)
    (* let _ = raise @@ InterExn "end" in *)
    let _ = mode := Oracle in
    let total_env = aux total_env 0 in
    let _ = save_result (benchname ^ "_oracle_maximal.json") total_env.preds names total_env in
    let result = spectable_filter_result names total_env.Env.spectable in
    Result result

  let find_weakened_model benchname ctx mii pre spectable =
    let bound_prefix = "bm_" in
    let union_table if_prefix result spectable =
      StrMap.fold (fun k v m ->
          let k = if if_prefix then bound_prefix^k else k in
          match StrMap.find_opt m k with
          | None -> StrMap.add k v m
          | Some _ -> raise @@ InterExn "union_table"
        ) result spectable in
    let make_constraint names = function
      | Ast.And ps ->
        let ps' = List.filter_map (fun p ->
            match p with
            | Ast.SpecApply (name', args) ->
              if List.exists (String.equal name') names
              then Some (Ast.SpecApply (bound_prefix ^ name', args))
              else None
            | Ast.Implies (_, _) -> None
            | _ -> raise @@ InterExn "never happen in make_constraint"
          ) ps in
        Ast.And ((Ast.Not (Ast.And ps')) :: ps)
      | _ -> raise @@ InterExn "never happen in make_constraint"
    in
    let consistent_file = sprintf "_%s/_consistent.json" benchname in
    let bound_file = sprintf "_%s/_bound_maximal.json" benchname in
    let consistent_result = try Some (Yojson.Basic.from_file consistent_file) with
      | _ -> None in
    let bound_result = try Some (Yojson.Basic.from_file bound_file) with
      | _ -> None in
    match consistent_result with
    | None -> printf "\tNone\n"
    | Some r ->
      (* let _ = printf "%s\n" consistent_file in *)
      let _, consistent_spectable = Env.decode_infer_result r in
      match bound_result with
      | None -> printf "%s: do not find weakening result\n" benchname
      | Some r ->
        (* let _ = printf "%s\n" bound_file in *)
        let _, bound_spectable = Env.decode_infer_result r in
        let names = StrMap.to_key_list bound_spectable in
        let pres = List.map Ast.merge_and @@ Ast.to_dnf @@ Ast.eliminate_cond_one pre in
        let pres' = List.map (fun pre -> make_constraint names pre) pres in
        (* let _ = List.iter (fun pre ->
         *     printf "%s\n" (Ast.vc_layout pre)
         *   ) pres' in
         * let _ = StrMap.iter (fun name spec ->
         *     printf "%s\n" (Ast.layout_spec_entry name spec)
         *   ) (union_table true consistent_spectable
         *        (union_table false bound_spectable spectable)) in *)
        let build_smt_query version =
          Ast.to_z3 ctx
            (Ast.And [Ast.Or pres'; mii.upost])
            (union_table true consistent_spectable
               (union_table false bound_spectable spectable))
            version mii.uvars
          (* Ast.to_z3 ctx
           *   (Ast.And [Ast.Or pres; mii.upost])
           *   ((union_table false bound_spectable spectable))
           *   version mii.uvars *)
        in
        let version = S.Z3aux.V2 in
        let smt_query = build_smt_query version in
        (* let _ = printf "%s\n" (Expr.to_string smt_query) in *)
        let r, delta_time = time (fun _ -> S.check ctx smt_query) in
        let res =
          match r with
          | S.SmtUnsat -> "Max"
          | S.Timeout -> "Timeout"
          | S.SmtSat _ ->
            sprintf "%.1f" (delta_time *. 1000.0)
        in
        let out_file = sprintf "_%s/_diff.json" benchname in
        Yojson.Basic.to_file out_file (`Assoc ["diff", `String res])


  let result benchname assertions spectable holel preds =
    let names = List.map (fun (hole, _) -> hole.name) holel in
    let program = "program:\n\n" in
    let library_functions = sprintf "F:\n%s\n" (StrList.to_string names) in
    let preds = sprintf "P:\n%s\n" (StrList.to_string preds) in
    let assertion =
      match assertions with
      | [a] ->
        sprintf "assertion:\n%s\n"
          (Ast.layout_spec
             (StrMap.find "result" spectable a))
      | [prea; posta] ->
        sprintf "assertion:\n%s\n=>\n%s\n"
          (Ast.layout_spec
             (StrMap.find "result" spectable prea))
          (Ast.layout_spec
             (StrMap.find "result" spectable posta))
      | _ -> raise @@ InterExn "never happen in result"
    in
    let resultfilename = sprintf "_remote_result/_%s/_bound_maximal.json"
        benchname in
    let result_to_file outc =
      try
        StrMap.iter (fun name spec ->
            fprintf outc "%s\n" (Ast.layout_spec_entry name spec)
          )
          (snd @@
           Env.decode_infer_result (Yojson.Basic.from_file resultfilename))
      with
      | _ -> fprintf outc "cex\n"
    in
    let outfile = sprintf "_final_result/_%s.text" benchname in
    let outc = open_out outfile in
    let _ = fprintf outc "%s\n%s\n%s\n%s\nresult:\n"
        program library_functions preds
        assertion in
    let _ = result_to_file outc in
    let _ = close_out outc in
    ()

  let do_consistent ?snum:(snum = None) ?uniform_qv_num:(uniform_qv_num = 2)
      benchname ctx mii pre spectable holel preds startX =
    let benchname = "_" ^ benchname ^ "/" in
    let _ = make_dir benchname in
    let _ = handle_snum snum in
    let names = List.map (fun (hole, _) -> hole.name) holel in
    let pres = List.map Ast.merge_and @@ Ast.to_dnf @@ Ast.eliminate_cond_one pre in
    let pres = List.sort (fun a b ->
        compare (Ast.conj_length b) (Ast.conj_length a)
      ) pres in
    let _ = List.iter (fun pre ->
        printf "[pre]\n%s\n" (Ast.vc_layout pre)
      ) pres in
    (* let _ = Ast.print_spectable spectable in *)
    let c = List.fold_left (fun c pre -> c + (Ast.count_apps pre names)) 0 pres in
    let _ = printf "#R:\n%i\n" c in
    (* let _ = raise @@ InterExn "end" in *)
    let env = consistent_solution ctx benchname
        mii pres spectable holel preds startX in
    match env with
    | CRCex ms ->
      let _ = printf "CEX:\n" in
      let _ = List.iter (fun m ->
          printf "%s\n"
            (List.to_string (fun (name, value) ->
                 sprintf "%s -> %s" name (V.layout value)
               ) (StrMap.to_kv_list m))
        ) ms in
      Cex ms
    | CRFinalEnv env ->
      let _ = StrMap.iter (fun name env ->
          printf "[%s] space: 2^%i = %i\n"
            name (List.length env.fset) (pow 2 (List.length env.fset))
        ) env.spec_envs in
      let _ = save_result (benchname ^ "_consistent.json") preds names env.vc in
      (* let _ = raise @@ InterExn "end" in *)
      let single_envs = List.map (fun specname ->
          let target_hole = StrMap.find "multi_infer" env.holes specname in
          let spec_env = StrMap.find "multi_infer" env.spec_envs specname in
          let single_env =
            make_single_abd_env env.vc spec_env target_hole preds uniform_qv_num
          in
          single_env
        ) names in
      let midfile = benchname ^ "_" ^ "beforeweakening.json" in
      let _ = Yojson.Basic.to_file midfile
          (Env.encode_weakening (env.vc, single_envs)) in
      let result = spectable_filter_result names env.vc.Env.spectable in
      Result result

  let do_weakening ctx benchname =
    let benchname = "_" ^ benchname ^ "/" in
    let midfile = benchname ^ "_" ^ "beforeweakening.json" in
    let _ = printf "before decode(%s)\n" midfile in
    let total_env, single_envs = Env.decode_weakening @@ Yojson.Basic.from_file midfile in
    let _ = printf "flow\n" in
    let _ = List.map (fun fl -> printf "flow:%s\n" (Ast.layout fl.Env.pre_flow)) total_env.multi_pre in
    weakening ctx benchname total_env single_envs time_bound

 let multi_infer ?snum:(snum = None) ?uniform_qv_num:(uniform_qv_num = 2)
     benchname ctx mii pre spectable holel preds startX =
   let _ = do_consistent ~snum:snum ~uniform_qv_num:uniform_qv_num benchname
       ctx mii pre spectable holel preds startX in
   do_weakening ctx benchname
      (* weakening ctx benchname env.vc single_envs time_bound *)
      (* let single_envs_arr = Array.of_list single_envs in
       * let rec aux total_env idx =
       *   if idx >= Array.length single_envs_arr
       *   then total_env
       *   else
       *     let single_env = single_envs_arr.(idx) in
       *     let single_result, delta_time =
       *       time (fun _ -> Single_abd.infer ctx total_env single_env time_bound) in
       *     let _ = printf "time: single: %s: %fs\n" single_env.Env.hole.name delta_time in
       *     match single_result with
       *     | Env.AlreadyMaxed -> aux total_env (idx + 1)
       *     | Env.MayAlreadyMaxed -> aux total_env (idx + 1)
       *     | Env.NewMaxed (total_env, single_env') ->
       *       let _ = Array.set single_envs_arr idx single_env' in
       *       aux total_env (idx + 1)
       *     | Env.Weaker (total_env, single_env') ->
       *       let _ = Array.set single_envs_arr idx single_env' in
       *       aux total_env (idx + 1)
       * in
       * let total_env = aux env.vc 0 in
       * let result = spectable_filter_result names total_env.spectable in
       * let _ = Yojson.Basic.to_file (name ^ "_" ^ "maximal.json")
       *     (Ast.spectable_encode result) in
       * result *)

 let do_full ?snum:(snum = None) ?uniform_qv_num:(uniform_qv_num = 2)
     benchname ctx mii pre spectable holel preds startX =
   let e = do_consistent ~snum:snum ~uniform_qv_num:uniform_qv_num benchname
       ctx mii pre spectable holel preds startX in
   match e with
   | Cex _ -> e
   | _ ->
     do_weakening ctx benchname

end
