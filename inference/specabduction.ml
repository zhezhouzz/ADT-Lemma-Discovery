module SpecAbduction = struct
  module LH = Language.Helper
  module P = Pred.Pred
  module V = Pred.Value
  module Ast = Language.SpecAst
  module Epr = Ast.E
  module SE = Epr.SE
  module S = Solver
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

  let default_range = [1;2;3]
  let default_qv_range = 0 :: default_range

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

  let sampling hole imp env num =
    let _ = printf "sampling %s\n" hole.name in
    let _, current_epr = env.abduciable in
    let _, inputs = get_inputs hole in
    let _ = printf "args = %s\n" (List.to_string T.layouttvar hole.args) in
    let _ = printf "inputs = %s\n" (List.to_string T.layouttvar inputs) in
    let inputtps,_ = List.split inputs in
    let samples = R.gens ~chooses:default_range ~num:num
        ~tps:inputtps ~bound: samplebound in
    let samples = List.filter_map (fun input ->
        let output = imp input in
        match output with
        | Some output -> Some (input @ output)
        | None -> None
      ) samples in
    let qvtypes, _ = List.split env.qv in
    let qvsamples = R.gens ~chooses:default_qv_range ~num:(List.length samples)
        ~tps:qvtypes ~bound: samplebound in
    let s = List.combine samples qvsamples in
    let _ = List.iter (fun (s1,s2) -> printf "{%s},{%s}]\n"
                          (List.to_string V.layout s1)
                          (List.to_string V.layout s2)) s in
    let extract_fv (args_value, qv_value) =
      let m = StrMap.empty in
      let m = List.fold_left (fun m ((_, name), v) ->
          StrMap.add name v m
        ) m (List.combine hole.args args_value) in
      let m = List.fold_left (fun m ((_, name), v) ->
          StrMap.add name v m
        ) m (List.combine env.qv qv_value) in
      if Epr.exec current_epr m
      then None
      else Some (List.map (fun feature -> F.exec feature m) env.fset)
    in
    let fvs = List.filter_map extract_fv s in
    let _ = printf "len(fvs) = %i\n" (List.length fvs) in
    let _ = List.iter (fun fv ->
        match Hashtbl.find_opt env.fvtab fv with
        | Some MultiPos -> ()
        | Some MultiMayNegCache -> raise @@ InterExn "never happen sampling"
        | Some MultiMayNeg -> Hashtbl.replace env.fvtab fv MultiPos
        | None -> Hashtbl.add env.fvtab fv MultiPos
      ) fvs in
    List.length fvs

  let gather_neg_fvec_to_tab ctx hole env applied_args qvrange model =
    let se_range = List.map (fun x -> SE.Literal (T.Int, SE.L.Int x)) qvrange in
    let sub_assignment = List.map (fun _ -> se_range) env.qv in
    let _, names = List.split (hole.args @ env.qv) in
    let counter = ref 0 in
    let _ =
      List.map (fun args ->
          let args = List.map SE.from_tpedvar args in
          let _ = printf "args:%s\n" (List.to_string SE.layout args) in
          let extract_fvec _ values =
            let vec = List.map
                (fun feature ->
                   Epr.subst (F.to_epr feature) names (args @ values)) env.fset in
            (* let _ = printf "[vec]:%s\n" (List.to_string Epr.layout vec) in *)
            let vec' = List.map (fun e -> S.get_pred model (Epr.to_z3 ctx e)) vec in
            (* let _ = printf "[vec]:%s%s\n" (List.to_string Epr.layout vec)
             *     (boollist_to_string vec') in *)
            match Hashtbl.find_opt env.fvtab vec' with
            | Some MultiMayNeg ->
              raise @@ InterExn "never happen gather_neg_fvec_to_tab"
            | Some MultiPos ->
              let _ = printf "pos:%s\n"  (boollist_to_string vec') in
              ()
            | Some MultiMayNegCache ->
              let _ = counter := !counter + 1 in
              let _ = printf "may neg cache:%s\n"  (boollist_to_string vec') in
              ()
            | None ->
              let _ = counter := !counter + 1 in
              let _ = printf "neg:%s\n"  (boollist_to_string vec') in
              Hashtbl.add env.fvtab vec' MultiMayNegCache
          in
          let _ = List.choose_list_list_order_fold extract_fvec () sub_assignment in
          ()
        ) applied_args in
    !counter


  (* let print_feature model ctx pred dt intvalue =
   *   printf "%s(%s, %i) = %b\n" pred dt intvalue
   *     (S.get_pred model
   *        (Epr.to_z3 ctx
   *           (Epr.Atom
   *              (SE.Op (T.Int, pred,
   *                      [SE.Var (T.IntList, dt); SE.Literal (T.Int, SE.L.Int intvalue)])
   *              )
   *           )
   *        )
   *     ) *)

  (* let show_all_features ctx model qv qvrange preds bpreds =
   *   let _ = printf "model\n%s\n" (Model.to_string model) in
   *   let _ = printf "show_all:bound:%s\n" (IntList.to_string qvrange) in
   *   (\* let _ = printf "show_all:\nnu_top=%i\n" (S.get_int_name ctx model "nu_top") in *\)
   *   let dts = [T.IntTree, "tr";T.IntTree, "a"; T.IntTree, "b";] in
   *   let aux dt =
   *     let tab = Hashtbl.create 1000 in
   *     let all_features = F.make_set_from_preds_multidt preds bpreds
   *         (dt :: qv) in
   *     let se_range = List.map (fun x -> SE.Literal (T.Int, SE.L.Int x)) qvrange in
   *     let sub_assignment = List.map (fun _ -> se_range) qv in
   *     let _, names = List.split qv in
   *     let _ = printf "dt:%s %s\n" (snd dt) (F.layout_set all_features) in
   *     let extract_fvec _ values =
   *       let vec = List.map
   *           (fun feature -> Epr.subst (F.to_epr feature) names values) all_features in
   *       (\* let _ = printf "%s\n" (List.to_string Epr.layout vec) in *\)
   *       let vec = List.map (fun e -> S.get_pred model (Epr.to_z3 ctx e)) vec in
   *       let _ = printf "u = %s: %s\n"
   *           (List.to_string SE.layout values) (boollist_to_string vec) in
   *       match Hashtbl.find_opt tab vec with
   *       | Some _ -> ()
   *       | None -> Hashtbl.add tab vec ()
   *     in
   *     let _ = List.choose_list_list_order_fold extract_fvec () sub_assignment in
   *     (\* let _ = Hashtbl.iter (fun vec _ ->
   *      *     printf "vec: %s\n" (boollist_to_string vec)
   *      *   ) tab in *\)
   *     ()
   *   in
   *   List.map aux dts *)

  (* let join_pos_neg_table pos neg candidate =
   *   let _ = Hashtbl.iter (fun vec _ ->
   *       match Hashtbl.find_opt pos vec with
   *       | Some _ -> Hashtbl.remove candidate vec
   *       | None -> ()) candidate in
   *   let negnum = Hashtbl.length candidate in
   *   let _ = Hashtbl.iter (fun vec _ ->
   *       match Hashtbl.find_opt neg vec with
   *       | Some _ ->
   *         let _ =
   *           printf "conflict:\n\t%s\n" (boollist_to_string vec);
   *           printf "candidate:\n";
   *           Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) candidate;
   *           printf "neg:\n";
   *           Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) neg
   *         in
   *         (\* () *\)
   *         raise @@ InterExn "bad error in join_pos_neg_table"
   *       | None -> Hashtbl.add neg vec ()) candidate in
   *   negnum *)

  let name_qv qv_num = List.map (fun n -> (T.Int, n)) @@ List.init qv_num (fun i -> sprintf "u_%i" i)

  let init_spec_env hole preds bpreds numX =
    let qv = name_qv numX in
    let fset = F.make_set_from_preds_multidt preds bpreds
        (hole.args @ qv) in
    let _ = printf "init-set:%s\n" (F.layout_set fset) in
    let fvtab = Hashtbl.create 1000 in
    let abduciable = [], Epr.Not Epr.True in
    { dt = D.F;
     qv = qv;
     fset = fset;
     fvtab = fvtab;
     abduciable = abduciable;}

  let init_env (pre, post) spectable preds bpreds numX holel =
    let holes, imps = List.fold_left (fun (m, imp_m) (hole, imp) ->
        (StrMap.add hole.name hole m,
         StrMap.add hole.name imp imp_m)
      ) (StrMap.empty, StrMap.empty) holel in
    let multi_pre =
      List.map (fun pre ->
          let applied_args_map = StrMap.mapi (fun name _ ->
              List.map (fun args ->
                  List.map SE.to_tpedvar args
                ) (Ast.get_app_args pre name)
            ) holes in
          let applied_args_map = StrMap.filter (fun _ r ->
              match r with
              | [] -> false
              | _ -> true
            ) applied_args_map in
          {Env.pre_flow = pre; Env.applied_args_map = applied_args_map}
        ) pre in
    let spec_envs = StrMap.map (fun hole ->
        init_spec_env hole preds bpreds numX
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
      Env.multi_pre =  multi_pre;
      Env.post = post;
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
    let abduciable = Epr.simplify_ite abduciable in
    let _ = printf "\traw abduciable:\n%s\n" (Epr.pretty_layout_epr abduciable) in
    let abduciable = env.qv, abduciable in
    {env with abduciable = abduciable; dt = dtidx}

  let inplace_gather_fv ctx model qvrange env flow =
    let total_neg_num = ref 0 in
    let _ = StrMap.iter
        (fun specname applied_args ->
           let hole = StrMap.find "update_spec_env" env.holes specname in
           let spec_env = StrMap.find "update_spec_env" env.spec_envs specname in
           let neg_num =
             gather_neg_fvec_to_tab ctx hole spec_env applied_args qvrange model
           in
           (* let _ = printf "total_neg_num:%i neg_num:%i\n"
            *     (!total_neg_num) neg_num in *)
           let _ = total_neg_num := !total_neg_num + neg_num in
           ()
        ) flow.Env.applied_args_map in
    let _ = printf "total_neg_num:%i\n" (!total_neg_num) in
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

  let is_verified = function
    | Verified -> true
    | _ -> false
  let is_cannot_gather = function
    | CannotGather -> true
    | _ -> false

  let inplace_verify_and_gather_fv ctx env flow =
    let smt_query = Ast.to_z3 ctx
        (Ast.Not (Ast.Implies (flow.Env.pre_flow, env.vc.Env.post)))
        env.vc.Env.spectable in
      match S.check ctx smt_query with
      | S.SmtUnsat -> Verified
      | S.Timeout ->
        let _ = printf "%s\n" (Expr.to_string smt_query) in
        raise (InterExn "multi inference time out!")
      | S.SmtSat model ->
        let qvrange = S.Z3aux.get_preds_interp model in
        (match inplace_gather_fv ctx model qvrange env flow with
         | None -> Gathered
         | Some pre ->
           let _ = printf "smt_query\n%s\n" (Expr.to_string smt_query) in
           let _ = printf "model:\n%s\n" (Model.to_string model) in
           (printf "cannot gather fv in ast:%s\n" (Ast.vc_layout pre); CannotGather)
        )

  let sample_num = 10

  let negcache_to_neg env =
    StrMap.iter (fun _ spec_env ->
        Hashtbl.filter_map_inplace (fun _ label ->
            match label with
            | MultiPos -> Some MultiPos
            | MultiMayNeg | MultiMayNegCache -> Some MultiMayNeg
          ) spec_env.fvtab
      ) env.spec_envs

  let refinement_loop ctx env =
    let _ = printf "refinement_loop\n" in
    let rec neg_refine_loop env =
      let _ = loop_counter := !loop_counter + 1 in
      (* let (fvs, res) = List.fold_left (fun (fvs, res) flow ->
       *     let (fvs, r) = inplace_verify_and_gather_fv ctx env flow fvs in
       *     fvs, res @ [r]
       *   ) (Hashtbl.create 1000, []) env.vc.Env.multi_pre in *)
      let res = List.map (fun flow ->
          inplace_verify_and_gather_fv ctx env flow
        ) env.vc.Env.multi_pre in
      if List.for_all is_verified res
      then Some env
      else if List.exists is_cannot_gather res
      then None
      else
        let _ = negcache_to_neg env in
        let spec_envs' = StrMap.map learn_in_spec_env env.spec_envs in
        let env = {env with spec_envs = spec_envs'} in
        let env = update_env_spectable env in
        neg_refine_loop env
    in
    let rec pos_refine_loop env =
      let total_pos_num = ref 0 in
      let spec_envs' = StrMap.mapi (fun specname spec_env ->
          let hole = StrMap.find "pos_refine_loop" env.holes specname in
          let imp = StrMap.find "pos_refine_loop" env.imps specname in
          let pos_num = sampling hole imp spec_env sample_num in
          let _ = total_pos_num := !total_pos_num + pos_num in
          let spec_env = learn_in_spec_env spec_env in
          spec_env
        ) env.spec_envs
      in
      if !total_pos_num > 0
      then
        let env = {env with spec_envs = spec_envs'} in
        let env = update_env_spectable env in
        let env = neg_refine_loop env in
        match env with
        | Some env -> pos_refine_loop env
        | None -> None
      else
        Some env
    in
    pos_refine_loop env

  let instantiate_bool pre (holes:(hole * (V.t list -> V.t list option)) list) =
    Ast.(
    let update t specname (specname_true, specname_false) =
      let rec aux t =
        match t with
        | ForAll _ -> raise @@ InterExn "never happen in instantiate_bool"
        | Implies (p1, p2) -> Implies (aux p1, aux p2)
        | And ps -> And (List.map aux ps)
        | Or ps -> Or (List.map aux ps)
        | Not p -> Not (aux p)
        | Iff (p1, p2) -> Iff (aux p1, aux p2)
        | Ite (SpecApply (specname', args), p2, p3) ->
          if String.equal specname' specname
          then
            match args with
            | [] -> raise @@ InterExn "never happen in instantiate_bool"
            | _ :: args ->
              Or [And [SpecApply(specname_true, args); aux p2];
                  And [SpecApply(specname_false, args); aux p3];]
          else Ite (SpecApply (specname', args), aux p2, aux p3)
        | Ite (_, _, _) ->
          raise @@ InterExn "never happen in instantiate_bool"
        | SpecApply (specname', args) ->
          if String.equal specname specname' then
            match args with
            | [] -> raise @@ InterExn "never happen in instantiate_bool"
            | b :: args ->
              Or [And [SpecApply(specname_true, args); is_true b];
                  And [SpecApply(specname_false, args); is_false b];]
          else
            t
      in
      aux t
    in
    let if_cond t specname =
      let rec aux t =
        match t with
        | ForAll _ -> raise @@ InterExn "never happen in instantiate_bool"
        | Implies (p1, p2) -> (aux p1) || (aux p2)
        | And ps -> List.exists aux ps
        | Or ps -> List.exists aux ps
        | Not p -> aux p
        | Iff (p1, p2) -> (aux p1) || (aux p2)
        | Ite (SpecApply (specname', _), p2, p3) ->
          (String.equal specname' specname) || (aux p2) || (aux p3)
        | Ite (_, _, _) ->
          raise @@ InterExn "never happen in instantiate_bool"
        | SpecApply (_, _) -> false
      in
      aux t
    in
    let rec update_holes (t, holes') = function
      | [] -> (t, holes')
      | (h, imp) :: r ->
        if if_cond t h.name
        then
          match h.args with
          | [] -> raise @@ InterExn "never happen in instantiate_bool"
          | _ :: args ->
            let specname_true = h.name ^ "#t" in
            let specname_false = h.name ^ "#f" in
            let insted_imp b = fun inp ->
              match imp inp with
              | None -> None
              | Some [V.B b'] -> if b == b' then Some [] else None
              | _ -> raise @@ InterExn "never happen in instantiate_bool"
            in
            let holes' =
              ({name = specname_true; args = args}, insted_imp true) ::
              ({name = specname_false; args = args}, insted_imp false) ::
              holes' in
            let t = update t h.name (specname_true, specname_false) in
            update_holes (t, holes') r
        else
          update_holes (t, (h, imp) :: holes') r
    in
    let t, holes = update_holes (pre, []) holes in
    t, holes
  )

  let init_unknown_fv fset =
    List.init (List.length fset) (fun i -> T.Bool, Printf.sprintf "_fv!%i" i)

  let make_single_abd_env vc_env spec_env hole =
    let _ = Printf.printf "|Fset| = %i\n" (List.length spec_env.fset) in
    let spec = StrMap.find "miss current single abd"
        vc_env.Env.spectable hole.name in
    let current =
      {Env.init_spec = spec;
       Env.init_dt = spec_env.dt;
       Env.additional_spec = spec;
       Env.additional_dt = spec_env.dt;
       (* Env.additional_spec = hole.args, (spec_env.qv, Epr.True);
        * Env.additional_dt = D.T *)
      } in
    let fvtab' = Hashtbl.create 10000 in
    let _ = Hashtbl.iter (fun vec label ->
        match label with
        | MultiPos -> Hashtbl.add fvtab' vec D.Pos
        | MultiMayNeg -> Hashtbl.add fvtab' vec D.MayNeg
        | MultiMayNegCache -> raise @@ InterExn "never happen in make_single_abd_env"
      ) spec_env.fvtab in
    let single_env = {
      Env.current = current;
      Env.qv = spec_env.qv;
      Env.fset = spec_env.fset;
      Env.hole = hole;
      Env.unknown_fv = init_unknown_fv spec_env.fset;
      Env.fvtab = fvtab';
    }
    in
    single_env

  let rec pow a = function
    | 0 -> 1
    | 1 -> a
    | n ->
      let b = pow a (n / 2) in
      b * b * (if n mod 2 = 0 then 1 else a)

  let consistent_solution ctx pres post spectable holel preds bpreds startX maxX =
    let rec search_hyp numX =
      if numX > maxX then
        None
      else
        let env = init_env (pres, post) spectable preds bpreds numX holel in
        match refinement_loop ctx env with
        | None -> search_hyp (numX + 1)
        | Some spec -> Some spec
    in
    search_hyp startX

  let merge_current sr fset =
    let spec, dt = D.merge_dt fset sr.Env.init_dt sr.Env.additional_dt in
    (* let spec, dt = D.subtract_dt fset sr.Env.additional_dt sr.Env.init_dt in *)
    spec, dt

  let merge_envs total_env single_envs_arr =
    Array.fold_left (fun total_env single_env ->
        let spec, _ = merge_current single_env.Env.current single_env.Env.fset in
        let abduciable = D.to_epr spec in
        let abduciable = Epr.simplify_ite abduciable in
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

  let verify_flow ctx vc flow =
    let smt_query = Ast.to_z3 ctx
        (Ast.Not (Ast.Implies (flow.Env.pre_flow, vc.Env.post)))
        vc.Env.spectable in
    match S.check ctx smt_query with
    | S.SmtUnsat -> true
    | S.Timeout ->
      let _ = printf "%s\n" (Expr.to_string smt_query) in
      raise (InterExn "multi inference time out!")
    | S.SmtSat _ -> false

  let verify ctx vc =
    let res = List.map (fun flow -> verify_flow ctx vc flow) vc.Env.multi_pre in
    List.for_all (fun x -> x) res

  let multi_infer ctx pre post spectable holel preds bpreds startX maxX =
    let pre, holel = instantiate_bool pre holel in
    let pres = List.map Ast.merge_and @@ Ast.to_dnf @@ Ast.eliminate_cond_one pre in
    let _ = List.iter (fun pre ->
        printf "[pre]\n%s\n" (Ast.vc_layout pre)
      ) pres in
    let _ = Ast.print_spectable spectable in
    let env = consistent_solution ctx pres post spectable holel preds bpreds startX maxX in
    match env with
    | None -> raise @@ InterExn "search_hyp: quantified variables over bound"
    | Some env ->
      let _ = StrMap.iter (fun name spec ->
          printf "%s\n" (Ast.layout_spec_entry name spec)
        ) env.vc.Env.spectable in
      let _ = StrMap.iter (fun name env ->
          printf "[%s] space: 2^%i = %i\n"
            name (List.length env.fset) (pow 2 (List.length env.fset))
        ) env.spec_envs in
      (* let _ = raise @@ InterExn "end" in *)
      let single_envs = StrMap.fold (fun specname spec_env r ->
          let target_hole = StrMap.find "multi_infer" env.holes specname in
          let single_env = make_single_abd_env env.vc spec_env target_hole in
          single_env :: r
        ) env.spec_envs [] in
      let single_envs = sort_singles_by_fset single_envs in
      let single_envs_arr = Array.of_list single_envs in
      let rec aux total_env idx =
        if idx >= Array.length single_envs_arr
        then total_env
        else
        let single_env = single_envs_arr.(idx) in
        match Single_abd.infer ctx total_env single_env with
        | None -> aux total_env (idx + 1)
        | Some (total_env, single_env') ->
          let _ = Array.set single_envs_arr idx single_env' in
          aux total_env (idx + 1)
      in
      let total_env = aux env.vc 0 in
      let total_env = merge_envs total_env single_envs_arr in
      let if_verified = verify ctx total_env in
      let _ = printf "verify merged:%b\n" if_verified in

      let top_spec = StrMap.find "update_env" env.spec_envs "top" in
      let top_hole = StrMap.find "update_env" env.holes "top" in
      let spectable' = StrMap.update "top" (fun spec ->
          match spec with
          | None -> raise @@ InterExn "update_env"
          | Some _ -> Some (top_hole.args, top_spec.abduciable)
        ) total_env.spectable in
      let total_env = {total_env with spectable = spectable'} in
      let if_verified = verify ctx total_env in
      let _ = printf "verify merged/top:%b\n" if_verified in

      let push_spec = StrMap.find "update_env" env.spec_envs "push" in
      let push_hole = StrMap.find "update_env" env.holes "push" in
      let spectable' = StrMap.update "push" (fun spec ->
          match spec with
          | None -> raise @@ InterExn "update_env"
          | Some _ -> Some (push_hole.args, push_spec.abduciable)
        )   total_env.spectable in
      let total_env = {total_env with spectable = spectable'} in
      let if_verified = verify ctx total_env in
      let _ = printf "verify merged/top/push:%b\n" if_verified in
      let _ = StrMap.iter (fun name spec ->
          printf "%s\n" (Ast.layout_spec_entry name spec)
        ) total_env.spectable in
      total_env


  (* let single_envs = List.rev single_envs in *)
  (* let _ = raise @@ InterExn "end" in *)
  (* let concat_env = List.find "multi_infer" (fun x ->
   *     String.equal "push" x.Env.hole.name) single_envs in
   * let _ = Single_abd.infer ctx env.vc concat_env in
   * let _ = raise @@ InterExn "end" in *)

      (* let single_envs = Array.of_list single_envs in
       * let rec check_all () =
       *   let rec aux total_env idx changenum =
       *     if idx == Array.length single_envs then total_env, changenum else
       *       let total_env, changenum =
       *         match Single_abd.infer ctx total_env single_envs.(idx) with
       *         | Some (total_env, single_env) ->
       *           let _ = Single_abd.refresh_single_abd_env single_env in
       *           let _ = Array.set single_envs idx single_env in
       *           let total_env = Single_abd.update_vc_env total_env single_env in
       *           (\* let _ = printf "updated total env\n" in
       *            * let _ = StrMap.iter (fun name spec ->
       *            *     printf "%s\n" @@ Ast.layout_spec_entry name spec
       *            *   ) total_env.spectable in *\)
       *           total_env, changenum + 1
       *         | None -> total_env, changenum
       *       in
       *       aux total_env (idx + 1) changenum
       *   in
       *   let total_env, changenum = aux env.vc 0 0 in
       *   if changenum == 0 then total_env else total_env
       *       (\* check_all () *\)
       * in
       * let total_env = check_all () in
       * total_env *)
end
