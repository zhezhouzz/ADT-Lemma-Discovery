module type SpecAbduction = sig
  type max_env = {
    spectable: Language.SpecAst.spec Utils.StrMap.t;
    phi: (Tp.Tp.t * string) list * Language.SpecAst.spec Utils.StrMap.t;
    hole: (Tp.Tp.t * string) list * Language.SpecAst.spec Utils.StrMap.t;
    qv: string list;
  }
  val infer:
    ctx:Z3.context ->
    vc:Language.SpecAst.t ->
    spectable:Language.SpecAst.spec Utils.StrMap.t ->
    hole: string ->
    preds: string list ->
    startX:int->
    maxX:int->
    samples: (Pred.Value.t Utils.StrMap.t) list ->
    Language.SpecAst.spec option

  val multi_infer:
    ctx:Z3.context ->
    pre:Language.SpecAst.t ->
    post:Language.SpecAst.t ->
    spectable:Language.SpecAst.spec Utils.StrMap.t ->
    holes: Language.Helper.hole list ->
    holes_imp: (Pred.Value.t list -> Pred.Value.t list) Utils.StrMap.t ->
    preds: string list ->
    startX:int->
    maxX:int->
    Language.SpecAst.spec option

  val maximal_abduction: ctx:Z3.context -> menv:max_env -> unit
end

module SpecAbduction (D: Dtree.Dtree) = struct
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
  type hole_cache = {
    qv: (Tp.Tp.t * string) list;
    fvec_set: F.t list;
    applied_args: SE.t list list list;
    pos: (bool list, unit) Hashtbl.t;
    neg: (bool list, unit) Hashtbl.t;
    candidate_neg: (bool list, unit) Hashtbl.t;
    dt: F.t D.t;
    abduciable: Epr.forallformula;
    coabduciable: Epr.forallformula;
  }

  open Utils
  open Printf
  open Z3

  let loop_counter = ref 0

  let name_qv qv_num = List.map (fun n -> (T.Int, n)) @@ List.init qv_num (fun i -> sprintf "u_%i" i)

  (* feature vectors consistent with the sample *)
  let gather_pos_fvec_to_tab' qv feature_set sample tab =
    let data : V.t list = StrMap.to_value_list sample in
    let typed_data = List.map (fun v -> V.get_tp v, v) data in
    let make_summary l =
      List.fold_left (fun summary (tp, elem) ->
          let rec add summary =
            match summary with
            | (tp', elems) :: summary' ->
              if T.eq tp tp'
              then (tp', elem :: elems) :: summary'
              else (tp', elems) :: (add summary')
            | [] -> [(tp, [elem])]
          in
          add summary
        ) [] l
    in
    let qv_summary : (T.t * (string list)) list = make_summary qv in
    let data_summary : (T.t * (V.t list)) list = make_summary typed_data in
    let rec sub_assign qv_summary =
      match qv_summary with
      | [] -> []
      | (tp, names) :: qv_summary' ->
        match List.find_opt (fun (tp', _) -> T.eq tp tp') data_summary with
        | None -> raise @@ InterExn "find in gather_pos_fvec"
        | Some (_, values) ->
          let assigned_values = List.combination_l values (List.length names) in
          (assigned_values) :: (sub_assign qv_summary')
    in
    let sub_assignment = sub_assign qv_summary in
    let extract_fvec _ value_ll =
      let rec make_assignment m qv_summary ll =
        match (qv_summary, ll) with
        | [], [] -> m
        | ((_, names) :: qv_summary, values :: ll) ->
          let m =
            List.fold_left (fun m (k, v) ->
                StrMap.add k v m
              ) m (List.combine names values)
          in
          make_assignment m qv_summary ll
        | _, _ -> raise @@ InterExn "gather_pos_fvec"
      in
      let m = make_assignment StrMap.empty qv_summary value_ll in
      let vec = List.map (fun feature -> F.exec feature m) feature_set in
      Hashtbl.add tab vec ()
    in
    let _ = List.choose_list_list_order_fold extract_fvec () sub_assignment in
    let _ = Hashtbl.iter (fun vec _ ->
        printf "pos vec: %s\n" (boollist_to_string vec)
      ) tab in
    tab

  let default_range = [0;1;2;3]

  (* feature vectors consistent with the sample *)
  let gather_pos_fvec_to_tab args qv feature_set data tab =
    (* let _ = printf "%s\n" (List.to_string ) *)
    let data : V.t list list = List.map (fun v -> [v]) data in
    let int_range = List.map (fun x -> V.I x) default_range in
    let data' = List.map (fun _ -> int_range) qv in
    let sub_assignment = data @ data' in
    let _, names = List.split (args @ qv) in
    let extract_fvec _ values =
      let m =
        List.fold_left (fun m (k, v) ->
            StrMap.add k v m
          ) StrMap.empty (List.combine names values)
      in
      let vec = List.map (fun feature -> F.exec feature m) feature_set in
      let _ = printf "%s: %s\n" (List.to_string V.layout values) (boollist_to_string vec) in
      match Hashtbl.find_opt tab vec with
      | Some _ -> ()
      | None -> Hashtbl.add tab vec ()
    in
    let _ = List.choose_list_list_order_fold extract_fvec () sub_assignment in
    let _ = Hashtbl.iter (fun vec _ ->
        printf "pos vec: %s\n" (boollist_to_string vec)
      ) tab in
    tab

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

  (* feature vectors consistent with the cex *)
  let gather_neg_fvec_to_tab ctx model qv qvrange feature_set tab =
    (* let _ = printf "%s\n" (Z3.Model.to_string model) in *)
    let se_range = List.map (fun x -> SE.Literal (T.Int, SE.L.Int x)) qvrange in
    let sub_assignment = List.map (fun _ -> se_range) qv in
    let _, names = List.split qv in
    let extract_fvec _ values =
      let vec = List.map
          (fun feature -> Epr.subst (F.to_epr feature) names values) feature_set in
      (* let _ = printf "%s\n" (List.to_string Epr.layout vec) in *)
      let vec = List.map (fun e -> S.get_pred model (Epr.to_z3 ctx e)) vec in
      match Hashtbl.find_opt tab vec with
      | Some _ -> ()
      | None -> Hashtbl.add tab vec ()
    in
    let _ = List.choose_list_list_order_fold extract_fvec () sub_assignment in
    let _ = Hashtbl.iter (fun vec _ ->
        printf "neg vec: %s\n" (boollist_to_string vec)
      ) tab in
    tab


  let print_feature model ctx pred dt intvalue =
    printf "%s(%s, %i) = %b\n" pred dt intvalue
      (S.get_pred model
         (Epr.to_z3 ctx
            (Epr.Atom
               (SE.Op (T.Int, pred,
                       [SE.Var (T.IntList, dt); SE.Literal (T.Int, SE.L.Int intvalue)])
               )
            )
         )
      )

  let show_all_features ctx model qv qvrange preds bpreds =
    (* let _ = print_feature model ctx "list_member" "nu" 1 in
     * let _ = print_feature model ctx "list_member" "s1" 1 in
     * let _ = print_feature model ctx "list_member" "s2" 1 in
     * let _ = print_feature model ctx "list_head" "nu" 1 in
     * let _ = print_feature model ctx "list_head" "s1" 1 in
     * let _ = print_feature model ctx "list_head" "s2" 1 in *)
    let _ = printf "model\n%s\n" (Model.to_string model) in
    let _ = printf "show_all:bound:%s\n" (IntList.to_string qvrange) in
    (* let _ = printf "show_all:\nnu_top=%i\n" (S.get_int_name ctx model "nu_top") in *)
    let dts = [T.IntTree, "tr";T.IntTree, "a"; T.IntTree, "b";] in
    let aux dt =
      let tab = Hashtbl.create 1000 in
      let all_features = F.make_set_from_preds_multidt preds bpreds
          (dt :: qv) in
      let se_range = List.map (fun x -> SE.Literal (T.Int, SE.L.Int x)) qvrange in
      let sub_assignment = List.map (fun _ -> se_range) qv in
      let _, names = List.split qv in
      let _ = printf "dt:%s %s\n" (snd dt) (F.layout_set all_features) in
      let extract_fvec _ values =
        let vec = List.map
            (fun feature -> Epr.subst (F.to_epr feature) names values) all_features in
        (* let _ = printf "%s\n" (List.to_string Epr.layout vec) in *)
        let vec = List.map (fun e -> S.get_pred model (Epr.to_z3 ctx e)) vec in
        let _ = printf "u = %s: %s\n"
            (List.to_string SE.layout values) (boollist_to_string vec) in
        match Hashtbl.find_opt tab vec with
        | Some _ -> ()
        | None -> Hashtbl.add tab vec ()
      in
      let _ = List.choose_list_list_order_fold extract_fvec () sub_assignment in
      (* let _ = Hashtbl.iter (fun vec _ ->
       *     printf "vec: %s\n" (boollist_to_string vec)
       *   ) tab in *)
      ()
    in
    List.map aux dts

  let join_pos_neg_table pos neg candidate =
    let _ = Hashtbl.iter (fun vec _ ->
        match Hashtbl.find_opt pos vec with
        | Some _ -> Hashtbl.remove candidate vec
        | None -> ()) candidate in
    let negnum = Hashtbl.length candidate in
    let _ = Hashtbl.iter (fun vec _ ->
        match Hashtbl.find_opt neg vec with
        | Some _ ->
          let _ =
            printf "conflict:\n\t%s\n" (boollist_to_string vec);
            printf "candidate:\n";
            Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) candidate;
            printf "neg:\n";
            Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) neg
          in
          (* () *)
          raise @@ InterExn "bad error in join_pos_neg_table"
        | None -> Hashtbl.add neg vec ()) candidate in
    negnum

  (* feature vectors consistent with the cex *)
  let gather_neg_fvec_to_tab_multi args vc ctx model head cache qvrange tab =
    (* let _ = printf "%s\n" (Z3.Model.to_string model) in *)
    let se_range = List.map (fun x -> SE.Literal (T.Int, SE.L.Int x)) qvrange in
    let sub_assignment = List.map (fun _ -> se_range) cache.qv in
    let _, names = List.split (head.funtype @ cache.qv) in
    let _ = printf "gather_neg_fvec_to_tab_multi:\n%s\n%s\n"
        (Ast.layout vc)
        (List.to_string (fun l ->
             sprintf "%s\n" (List.to_string SE.layout l)
           ) args) in
    let _ =
      List.map (fun args ->
          let _ = printf "~%s\n"
              (List.to_string SE.layout args) in
          let extract_fvec _ values =
            let vec = List.map
                (fun feature ->
                   Epr.subst (F.to_epr feature) names (args @ values)) cache.fvec_set in
            let _ = printf "[vec]:%s\n" (List.to_string Epr.layout vec) in
            let vec' = List.map (fun e -> S.get_pred model (Epr.to_z3 ctx e)) vec in
            let _ = printf "[vec]:%s%s\n" (List.to_string Epr.layout vec)
                (boollist_to_string vec') in
            match Hashtbl.find_opt tab vec' with
            | Some _ -> ()
            | None -> Hashtbl.add tab vec' ()
          in
          let _ = List.choose_list_list_order_fold extract_fvec () sub_assignment in
          let _ = Hashtbl.iter (fun vec _ ->
              printf "neg vec: %s\n" (boollist_to_string vec)
            ) tab
          in
          ()
        ) args in
    tab

  let join_pos_neg_table_multi head hole candidate =
    let _ = Hashtbl.iter (fun vec _ ->
        match Hashtbl.find_opt hole.pos vec with
        | Some _ -> Hashtbl.remove candidate vec
        | None -> ()) candidate in
    let negnum = Hashtbl.length candidate in
    let if_overlap = Hashtbl.fold (fun vec _ if_overlap ->
        match Hashtbl.find_opt hole.neg vec with
        | Some _ ->
          let _ =
            printf "[%s]abd:\n%s\n" head.name (Epr.pretty_layout_forallformula hole.abduciable);
            printf "fset:\n%s\n" (F.layout_set hole.fvec_set);
            printf "conflict:\n\t%s\n" (boollist_to_string vec);
            printf "candidate:\n";
            Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) candidate;
            printf "neg:\n";
            Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) hole.neg;
            printf "pos:\n";
            Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) hole.pos
          in
        raise @@ InterExn "bad error in join_pos_neg_table"
        | None ->
          if_overlap) candidate false in
    if if_overlap then 0
    else
      (Hashtbl.iter (fun vec _ ->
           match Hashtbl.find_opt hole.candidate_neg vec with
           | Some _ -> ()
           | None -> Hashtbl.add hole.candidate_neg vec ()) candidate; negnum)

  let sample_filter hole_spec sample =
    List.map (fun (_, name) ->
        match StrMap.find_opt sample name with
        | None -> raise @@ InterExn "bad sample"
        | Some v -> v) hole_spec.funtype

  let pn_to_axiom_epr feature_set pos neg =
    let data = {FV.dfeature_set = feature_set;
                FV.labeled_vecs =
                  Hashtbl.fold (fun vec _ vecs -> (true, vec) :: vecs) pos @@
                  Hashtbl.fold (fun vec _ vecs -> (false, vec) :: vecs) neg []} in
    let res = D.classify data in
    (* let _ = printf "raw:%s\n" (D.layout res) in *)
    res

  let init_cache vcs preds bpreds hole_spec numX =
    let qv = name_qv numX in
    let fvec_set = F.make_set_from_preds_multidt preds bpreds
        (hole_spec.funtype @ qv) in
    let _ = printf "init-set:%s\n" (F.layout_set fvec_set) in
    let pos_tab = List.fold_left (fun tab sample ->
        gather_pos_fvec_to_tab hole_spec.funtype qv fvec_set sample tab
      ) (Hashtbl.create 1000) hole_spec.inout in
    (* let _ = printf "~~%s\n"
     *     (List.to_string (List.to_string SE.layout) (Ast.get_app_args vc hole_spec.name)) in *)
    {qv = qv;
     fvec_set = fvec_set;
     pos = pos_tab;
     neg = Hashtbl.create 1000;
     candidate_neg = Hashtbl.create 1000;
     abduciable = [], Epr.True;
     dt = D.T;
     applied_args = List.map (fun vc -> Ast.get_app_args vc hole_spec.name) vcs;
     coabduciable = [], Epr.True;
    }

  let cache_update_abd head hole =
    let _ = Hashtbl.iter (fun vec _ -> Hashtbl.add hole.neg vec ()) hole.candidate_neg in
    let _ = Hashtbl.clear hole.candidate_neg in
    let p_size, n_size = map_double Hashtbl.length (hole.pos, hole.neg) in
    let _ = printf "infer %s\n" head.name in
    let _ = printf "\tnum:%i|%i\n" (Hashtbl.length hole.pos) (Hashtbl.length hole.neg) in
    (* let _ = if (!loop_counter) > 1 && String.equal head.name "t" then
     *     raise @@ InterExn "end" else () in *)
    let dt =
      if n_size == 0
      then D.T
      else if p_size == 0
      then D.F
      else pn_to_axiom_epr hole.fvec_set hole.pos hole.neg in
    let abduciable = D.to_epr dt in
    let _ = printf "\traw abduciable:%s\n" (Epr.layout abduciable) in
    (* let _ = if (!loop_counter) > 1 && String.equal head.name "t" then
     *     raise @@ InterExn "end" else () in *)
    let abduciable = Epr.simplify_ite abduciable in
    let abduciable = hole.qv, abduciable in
    let _ =
      if String.equal head.name "StackTail"
      then
        ( printf "\tfset:%s\n" (F.layout_set hole.fvec_set);
          printf "\tabduciable:%s\n" (Epr.layout_forallformula abduciable);
          printf "pos:\n";
          Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) hole.pos;
          printf "neg:\n";
          Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) hole.neg)
      else ()
    in
    (* let _ = printf "\tabduciable:%s\n" (Epr.layout_forallformula abduciable) in *)
    {hole with abduciable = abduciable; dt = dt}

  let cache_update_model idx vc preds bpreds ctx model bounds head hole =
    let _ = printf "cache_update_model(%s):\n%s\n" (head.name) (F.layout_set hole.fvec_set) in
    let candidate_neg_tab =
      gather_neg_fvec_to_tab_multi
        (List.nth hole.applied_args idx) vc ctx model head hole bounds (Hashtbl.create 1000)
    in
    let _ = show_all_features ctx model [(T.Int, "u")] bounds preds bpreds in
    let negnum = join_pos_neg_table_multi head hole candidate_neg_tab in
    negnum

  let summary_traces holes traces =
    List.fold_left (fun holes trace ->
        List.fold_left (fun holes (specname, values) ->
            List.map (fun hole ->
                if String.equal hole.name specname
                then {hole with inout = values :: hole.inout}
                else hole
              ) holes
          ) holes trace
      ) holes traces

  let max_spec ctx vcs (spectable: Ast.spec StrMap.t) (head, hole) =
    let _ = printf "--max_spec--\n\n" in
    let _ = printf "[%s]:%s\n" head.name (Epr.layout_forallformula hole.abduciable) in
    let verify (spectable: Ast.spec StrMap.t) (head, hole) =
      let vc = Ast.neg_spec head.name (Or vcs) in
      let vc = Ast.implies_to_and vc in
      let spectable = StrMap.add ("co_" ^ head.name)
          (head.funtype, hole.coabduciable) spectable in
      let _ = printf "raw smt_query\n%s\n" (Ast.layout vc) in
      let _ = StrMap.iter (fun name spec ->
          printf "%s\n" (Ast.layout_spec_entry name spec)) spectable in
      let smt_query = Ast.to_z3 ctx vc spectable in
      let _ = printf "smt_query\n%s\n" (Expr.to_string smt_query) in
      let valid, model = S.check ctx smt_query in
      if valid
      then None
      else
        let model = match model with
          | None -> raise @@ InterExn "bad spec abd"
          | Some model -> model in
        let bounds = get_preds_interp model in
        let candidate =
          gather_neg_fvec_to_tab_multi (List.flatten hole.applied_args) vc ctx model head hole bounds (Hashtbl.create 1000)
        in
        let _ = Hashtbl.filter_map_inplace (fun vec _ ->
            if D.exec_vector hole.dt hole.fvec_set vec
            then None
            else Some ()
          ) candidate in
        let _ = printf "%s\n" (F.layout_set hole.fvec_set) in
        let _ = Hashtbl.iter (fun vec _ ->
            printf "candidate: %s\n" (boollist_to_string vec)
          ) candidate in
        Some candidate
    in
    verify spectable (head, hole)

  let reset_cache candidate (head, cache) =
    let _ = Hashtbl.iter (fun vec _ ->
        match Hashtbl.find_opt cache.pos vec with
        | Some _ -> raise @@ InterExn "error in reset_cache"
        | None -> Hashtbl.add cache.pos vec ()
      ) candidate in
    let _ = Hashtbl.clear cache.candidate_neg in
    let _ = Hashtbl.clear cache.neg in
    (* let cache = {cache with neg = (Hashtbl.create 1000)} in *)
    let _ = printf "\tnum:%i|%i\n" (Hashtbl.length cache.pos) (Hashtbl.length cache.neg) in
    head, cache

  let block candidate (head, hole) =
    let ps =
    Hashtbl.fold (fun vec _ res ->
        let fs =
        List.map (fun (feature, b) ->
            if b then F.to_epr feature else Epr.Not (F.to_epr feature)
            ) (List.combine hole.fvec_set vec)
        in
        (Epr.And fs) :: res
        ) candidate []
    in
    head, {hole with coabduciable = hole.qv, (Epr.Not (Epr.And ps))}

  let refinement_loop ctx vcs spectable holes preds bpreds =
    let _ = printf "refinement_loop\n" in
    let verify spectable holes (idx, vc) =
      let _ = printf "raw smt_query\n%s\n" (Ast.layout vc) in
      let _ = List.map (fun (head, cache) ->
          printf "hole spec[%s]: %s\n" head.name (Epr.layout_forallformula cache.abduciable)
        ) holes in
      let smt_query = Ast.to_z3 ctx (Ast.Not vc) spectable in
      let _ = printf "smt_query\n%s\n" (Expr.to_string smt_query) in
      let valid, model = S.check ctx smt_query in
      if valid
      then true, holes
      else
        let model = match model with
          | None -> raise @@ InterExn "bad spec abd"
          | Some model -> model in
        let bounds = get_preds_interp model in
        let totalnum = List.fold_left (fun totalnum (head, hole) ->
            let negnum = cache_update_model idx vc preds bpreds ctx model bounds head hole in
            let _ = printf "update %s end\n" head.name in
            totalnum + negnum) 0 holes in
        let _ = if totalnum == 0 then raise @@ InterExn "bad model" else () in
        false, holes
    in
    let rec refine_loop holes =
      let _ = loop_counter := !loop_counter + 1 in
      let holes = List.map (fun (head, cache) -> head, cache_update_abd head cache) holes in
      let spectable =
        List.fold_left (fun spectable (head, cache) ->
            StrMap.add head.name
              (head.funtype, cache.abduciable) spectable
          ) spectable holes in
      let is_verified, holes =
        List.fold_lefti (fun (is_verified, holes) idx vc ->
            let b, holes = verify spectable holes (idx, vc) in
            is_verified && b, holes
          ) (true, holes) vcs in
      if is_verified then
        Some (spectable, holes)
      else
        refine_loop holes
    in
    refine_loop holes

  let multi_infer ctx vcs spectable hole_specs preds bpreds startX maxX traces =
    let hole_specs = summary_traces hole_specs traces in
    let rec search_hyp numX =
      if numX > maxX then
        raise @@ InterExn "search_hyp: quantified variables over bound"
      else
        let holes = List.map (fun hole ->
            hole, init_cache vcs preds bpreds hole numX) hole_specs in
        match refinement_loop ctx vcs spectable holes preds bpreds with
        | None -> search_hyp (numX + 1)
        | Some spec -> Some spec
    in
    search_hyp startX
end
