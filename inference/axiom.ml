module type AxiomSyn = sig
  type stat_neg_sample = {
    posvec:int; negvec:int; totalvec:int
  }
  type stat_pos_sample = {
    totalposvec:int; samplesize:int; postimes:int;
  }
  type stat_static_hyp = {numX:int;feature_set_size:int;}
  type stat_hyp = {
    static_hyp:stat_static_hyp;
    numIter:int;
    negSample:stat_neg_sample list;
    posSample:stat_pos_sample list;
    poshypvec:int;
    neghypvec:int;
  }
  type stat = stat_hyp list
  val layout_stat_hyp: stat_hyp -> string
  type stat_entry = {
    etr_numX:int;
    etr_numFeatureset:int;
    etr_numMainIter:int;
    etr_numCex:int;
    etr_num_pfev_in_negsample:int;
    etr_num_nfev_in_negsample:int;
    etr_num_totalfev_in_negsample:int;
    etr_num_sampling_iter:int;
    etr_num_possample:int;
    etr_num_pfev_in_possample:int;
  }
  val make_stat_entry: stat -> stat_entry
  val layout_entry: stat_entry -> string
  val infer:
    ctx:Z3.context ->
    vc:Language.SpecAst.t ->
    spectable:Language.SpecAst.spec Utils.StrMap.t ->
    preds: string list ->
    startX:int->
    maxX:int->
    sampledata:int ->
    stat * (Tp.Tp.t * Language.SpecAst.E.forallformula) option
end

module AxiomSyn (D: Dtree.Dtree) = struct
  type stat_neg_sample = {
    posvec:int; negvec:int; totalvec:int
  }
  type stat_pos_sample = {
    totalposvec:int; samplesize:int; postimes:int;
  }
  type stat_static_hyp = {numX:int;feature_set_size:int;}
  type stat_hyp = {
    static_hyp:stat_static_hyp;
    numIter:int;
    negSample:stat_neg_sample list;
    posSample:stat_pos_sample list;
    poshypvec:int;
    neghypvec:int;
  }
  type stat_entry = {
    etr_numX:int;
    etr_numFeatureset:int;
    etr_numMainIter:int;
    etr_numCex:int;
    etr_num_pfev_in_negsample:int;
    etr_num_nfev_in_negsample:int;
    etr_num_totalfev_in_negsample:int;
    etr_num_sampling_iter:int;
    etr_num_possample:int;
    etr_num_pfev_in_possample:int;
  }
  type stat = stat_hyp list
  module D = D
  module V = Pred.Value
  module P = Pred.Pred
  module Ast = Language.SpecAst
  module Epr = Ast.E
  module SE = Epr.SE
  module S = Solver
  module T = Tp.Tp
  module F = Feature.Feature
  module R = Randomgen.Randomgen
  module FastDT = Ml.FastDT.FastDT
  module RS = Sample.RealSample
  module FV = Sample.FeatureVector
  open Utils
  open Printf
  (* type vec = bool list
   * type value = Pred.Value.t *)
  (* type typed_var = (Tp.Tp.t * string) *)
  open Z3

  let make_static_stat_hyp fvnum feature_set =
    {numX = fvnum; feature_set_size = List.length feature_set}
  let make_stat_hyp fvnum feature_set =
    {static_hyp = make_static_stat_hyp fvnum feature_set;
     numIter = 0;
     posSample = [];
     negSample = [];
     poshypvec = 0;
     neghypvec = 0;}
  let update_negSample negSample numIter neg =
    let counter = Array.init (numIter + 1) (fun _ -> 0) in
    let _ = Hashtbl.iter (fun _ v ->
        Array.set counter v (counter.(v) + 1)
      ) neg in
    let negSample = List.mapi (fun i n ->
        {posvec = n.totalvec - counter.(i);
         negvec = counter.(i);
         totalvec = n.totalvec
        }
      ) negSample in
    negSample

  let layout_pos {totalposvec; samplesize; postimes} =
    sprintf "iter times: %i; sample size: %i; total pos vec:%i"
      postimes samplesize totalposvec

  let layout_neg {posvec; negvec; totalvec} =
    sprintf "pos vec: %i; neg vec: %i; total vec:%i" posvec negvec totalvec

  let layout_stat_hyp stat =
    sprintf "[numX=%i; feature_set_size=%i]\n[numIter=%i; total pos fvec:%i; total neg fvec:%i;]\npos samples:%s\nneg_samples:%s\n"
      stat.static_hyp.numX stat.static_hyp.feature_set_size
      stat.numIter stat.poshypvec stat.neghypvec
      (List.fold_left (fun r s -> sprintf "%s\n%s" r (layout_pos s)) "" stat.posSample)
      (List.fold_left (fun r s -> sprintf "%s\n%s" r (layout_neg s)) "" stat.negSample)
  let make_stat_entry stat =
    let etr_numMainIter = List.length stat in
    let stat = List.rev stat in
    match stat with
    | [] -> raise @@ InterExn "never happen"
    | last :: _ ->
      let etr_numX = last.static_hyp.numX in
      let etr_numFeatureset = last.static_hyp.feature_set_size in
      let aux {etr_numX; etr_numMainIter; etr_numFeatureset;
               etr_numCex;etr_num_pfev_in_negsample;etr_num_nfev_in_negsample;
                 etr_num_totalfev_in_negsample;etr_num_sampling_iter;
               etr_num_possample;etr_num_pfev_in_possample} stat_hyp =
        let etr_numCex = etr_numCex + List.length stat_hyp.negSample in
        let etr_num_nfev_in_negsample = etr_num_nfev_in_negsample + stat_hyp.neghypvec in
        let ntotal = List.fold_left (fun r s -> s.totalvec + r) 0 stat_hyp.negSample in
        let etr_num_totalfev_in_negsample = etr_num_totalfev_in_negsample + ntotal in
        let etr_num_pfev_in_negsample = etr_num_pfev_in_negsample +
                                        (ntotal - stat_hyp.neghypvec) in
        let etr_num_sampling_iter, etr_num_possample, etr_num_pfev_in_possample =
          List.fold_left (fun (niter, npsample, npfvec) s ->
              (niter + s.postimes, npsample + s.samplesize, npfvec + s.totalposvec))
            (etr_num_sampling_iter, etr_num_possample, etr_num_pfev_in_possample)
            stat_hyp.posSample in
        {etr_numX; etr_numMainIter; etr_numFeatureset;
         etr_numCex;
         etr_num_pfev_in_negsample;etr_num_nfev_in_negsample;etr_num_totalfev_in_negsample;
         etr_num_sampling_iter;etr_num_possample;etr_num_pfev_in_possample}
      in
      List.fold_left aux
        {etr_numX; etr_numMainIter; etr_numFeatureset;
         etr_numCex = 0;etr_num_pfev_in_negsample = 0;etr_num_nfev_in_negsample = 0;
         etr_num_totalfev_in_negsample = 0;etr_num_sampling_iter = 0;
         etr_num_possample = 0;etr_num_pfev_in_possample = 0} stat

  let layout_entry stat_entry =
    sprintf "$%i$ & $%i$ & $%i$ & $%i$ & $%i$ & $%i$ & $%i$ & $%i$ & $%i$ & $%i$"
      stat_entry.etr_numMainIter stat_entry.etr_numX stat_entry.etr_numFeatureset
      stat_entry.etr_numCex
      stat_entry.etr_num_pfev_in_negsample
      stat_entry.etr_num_nfev_in_negsample
      stat_entry.etr_num_totalfev_in_negsample
      stat_entry.etr_num_sampling_iter
      stat_entry.etr_num_possample
      stat_entry.etr_num_pfev_in_possample

  let max_main_loop_with_fixed_fv_times = 20

  (* let counter = ref max_main_loop_with_fixed_fv_times *)

  let check_unbounded_dts unbounded_dts =
    match unbounded_dts with
    | [] -> raise @@ UndefExn "unbounded_dts"
    | (tp, name) :: t ->
      tp, List.fold_left (fun r (tp', name') ->
          if T.eq tp' tp then name' :: r else
            raise @@ UndefExn "unbounded_dts"
        ) [name] t

  let interval ctx exists_fv (s, e) =
    let (s', e') =
      map_double (fun x -> Epr.SE.Literal (T.Int, Epr.SE.L.Int x)) (s, e) in
    let name_to_var name = SE.Var (T.Int, name) in
    let geE a b = Epr.Atom (SE.Op (T.Bool, ">=", [a; b])) in
    let interval = Epr.to_z3 ctx
        (Epr.And (List.fold_left (fun l u ->
             l @ [geE (name_to_var u) s'; geE e' (name_to_var u)]) [] exists_fv)) in
    interval

  let get_preds_const ctx model =
    (* let _ = printf "%s\n" (Z3.Model.to_string model) in *)
    let funcs = Model.get_func_decls model in
    let get func =
      match Model.get_func_interp model func with
      | None -> raise @@ InterExn "never happen"
      | Some interp ->
        (* let _ = printf "\tfunc:%s\n" (Symbol.to_string (FuncDecl.get_name func)) in *)
        let domain = FuncDecl.get_domain func in
        let codomain = FuncDecl.get_range func in
        let intsort = Arithmetic.Integer.mk_sort ctx in
        let get_int_consts (sort, e) =
          if (Sort.equal sort intsort) && ((Expr.get_num_args e) == 0) then
            (* let _ = printf "e=%s [%i]\n" (Expr.to_string e) (Expr.get_num_args e) in *)
            Some (S.get_int model e)
            (* match S.get_int model e with
             * | Some i -> Some i
             * | None -> raise @@ InterExn (sprintf "get_int_consts:%s" (Expr.to_string e)) *)
          else
            None
        in
        let consts_of_branchs =
          List.map (fun e ->
              Model.FuncInterp.FuncEntry.(
                (get_int_consts (codomain, get_value e))::
                (List.map get_int_consts (List.combine domain (get_args e)))
              )
            ) (Model.FuncInterp.get_entries interp) in
        let elsebranch = get_int_consts (codomain, Model.FuncInterp.get_else interp) in
        let c = List.remove_duplicates_eq @@ List.filter_map (fun x -> x)
            (elsebranch :: (List.flatten consts_of_branchs))
        in
        c
    in
    let res = List.remove_duplicates_eq @@ List.flatten @@ List.map get funcs in
    let res = match IntList.max_opt res with
      | Some m -> (m + 1) :: res
      | None -> 0 :: res
    in
    (* let _ = printf "consts:%s\n" (IntList.to_string res) in *)
    res

  let get_preds_interp ctx model =
    let funcs = Model.get_func_decls model in
    (* let funcs =
     *   List.filter_map (fun info ->
     *       List.find_opt (fun func ->
     *           String.equal (Symbol.to_string (FuncDecl.get_name func)) info.P.raw_name
     *         ) funcs
     *     ) P.raw_preds_info
     * in *)
    (* let _ = List.iter (fun func -> printf "%s\n" (FuncDecl.to_string func)) funcs in *)
    let get func =
      match Model.get_func_interp model func with
      | None -> raise @@ InterExn "never happen"
      | Some interp ->
        let domain = FuncDecl.get_domain func in
        let argsname = List.init (Model.FuncInterp.get_arity interp)
            (fun i -> sprintf "x!%i" i) in
        let args = List.map (fun (n, sort) -> Expr.mk_const_s ctx n sort)
            (List.combine argsname domain) in
        let codomain = FuncDecl.get_range func in
        let nu = Expr.mk_const_s ctx "!nu" codomain in
        let application = Boolean.mk_eq ctx (FuncDecl.apply func args) nu in
        (* let _ = printf "app=%s\n" (Expr.to_string application) in *)
        let branchs =
          List.map (fun e ->
              Model.FuncInterp.FuncEntry.(
                (List.map (fun (a, b) -> Boolean.mk_eq ctx a b)
                   (List.combine args (get_args e)),
                 (Boolean.mk_eq ctx nu (get_value e))
                )
              )
            ) (Model.FuncInterp.get_entries interp) in
        let elsebranch = Boolean.mk_eq ctx nu @@ Model.FuncInterp.get_else interp in
        let body = List.fold_left (fun r (conds, v) ->
            Boolean.mk_ite ctx (Boolean.mk_and ctx conds) v r
          ) elsebranch branchs in
        let body =
          Quantifier.expr_of_quantifier
            (Quantifier.mk_forall_const ctx (nu :: args)
               (Boolean.mk_eq ctx application body)
               (Some 1)
               [] [] None None)
        in
        (* let _ = printf "%s\n" (Expr.to_string body) in *)
        body
    in
    List.map get funcs

  let neg_update_raw ctx pos neg model feature_set dt fv unbounded_dts =
    (* let _ = printf "%s\n" (Z3.Model.to_string model) in
     * let _ = get_preds_interp ctx model in
     * let _ = raise @@ InterExn "zz" in *)
    (* let _ = printf "%s\n" (Z3.Model.to_string model) in
     * let _ = printf "%s\n" (StrList.to_string unbounded_dts) in
     * let _ = raise @@ InterExn "zz" in *)
    let make_exists ctx forallvars body =
      if List.length forallvars == 0 then body else
        Quantifier.expr_of_quantifier
          (Quantifier.mk_exists_const ctx forallvars
             body
             (Some 1)
             [] [] None None)
    in
    let constraints = get_preds_interp ctx model in
    let make_query feature_vector =
      let body = List.fold_left (fun res (b, feature) ->
          let lit = Epr.to_z3 ctx (F.to_epr feature) in
          if b then lit :: res else (Z3.Boolean.mk_not ctx lit) :: res
        ) [] (List.combine feature_vector feature_set) in
      let dt_in_verification =
        Z3.Boolean.mk_or ctx @@
        List.map (fun n ->
            Z3.Boolean.mk_eq ctx (Z3.Arithmetic.Integer.mk_const_s ctx n)
              (Z3.Arithmetic.Integer.mk_const_s ctx (snd dt))
          ) unbounded_dts
      in
      let var = List.map (fun (_, n) -> Z3.Arithmetic.Integer.mk_const_s ctx n) (dt :: fv) in
      Boolean.mk_and ctx
        (
          (make_exists ctx var (Z3.Boolean.mk_and ctx (dt_in_verification :: body))) ::
          constraints
        )
    in
    (* let print_vec _ vec = printf "%s\n"
     *     (Array.fold_left (fun r b -> sprintf "%s %b" r b) "" vec) in
     * let _ = List.power_set_b_fold print_vec () (List.length feature_set) in
     * let _ = raise @@ InterExn "zz" in *)
    let if_neg = ref false in
    let aux _ vec =
      let v = Array.to_list vec in
      let q = make_query v in
      (* let _ = printf "q=%s\n" (Expr.to_string q) in
       * let _ = raise @@ InterExn "zz" in *)
      match Hashtbl.find_opt pos v, Hashtbl.find_opt neg v with
      | None, None ->
        (match S.check ctx q with
         | _, None -> ()
         | _, Some _ ->
           let _ = if_neg := true in
           (* let _ = printf "%s\n" (boollist_to_string v) in
            * let _ = printf "q=%s\n" (Expr.to_string q) in
            * let _ = raise @@ InterExn "zz" in *)
           Hashtbl.add neg v ()
        )
      | _, _ -> ()
    in
    let _ = List.power_set_b_fold aux () (List.length feature_set) in
    !if_neg

  let neg_update_raw2 ctx pos neg model feature_set _ fv unbounded_dts iternum =
    (* let _ = printf "neg_update_raw2\n" in *)
    (* let _ = printf "%s\n" (Z3.Model.to_string model) in *)
    let consts = get_preds_const ctx model in
    let dtconsts = List.map (fun n ->
        SE.Literal (T.Int , SE.L.Int (S.get_int_name ctx model n))
      ) unbounded_dts in
    (* let _ =
     *   printf "dtconsts:%s\n" (List.to_string SE.layout dtconsts) in *)
    let assignments =
      List.map (fun l -> List.map (fun i -> SE.Literal (T.Int , SE.L.Int i)) l) @@
      List.remove_duplicates IntList.eq @@
      List.choose_list_list
        (List.init (List.length fv) (fun _ -> consts)) in
    (* let _ = List.iter (fun fvec ->
     *     printf "fvec:%s\n" (List.to_string SE.layout fvec))
     *     assignments in *)
    (* let dt = Arithmetic.Integer.mk_const_s ctx (snd dt) in *)
    let fv = List.map (fun (_, var) -> var) fv in
    let aux dtc c =
      let cc = List.combine fv c in
      let feature_to_q feature =
        let search n = snd @@ StrList.search "feature_to_q" cc n in
        match feature with
        | F.Bo _ -> raise @@ InterExn "never happen"
        | F.Base (op, a, b) ->
          (SE.Op (T.Bool, op, List.map search [a;b]))
        | F.Pr (p, [_], args) ->
          (SE.Op (T.Bool, p, dtc :: (List.map search args)))
        | F.Pr (_, _, _) -> raise @@ InterExn "never happen"
      in
      let feature_vector = List.map (fun feature ->
          let q = feature_to_q feature in
          (* let _ = printf "q=%s\n" (SE.layout q) in *)
          S.get_pred model (SE.to_z3 ctx q)
        ) feature_set in
      feature_vector
    in
    let auxs c = List.map (fun dtc -> aux dtc c) dtconsts in
    let feature_vectors = List.flatten @@ List.map auxs assignments in
    let feature_vectors =
      List.remove_duplicates
        (fun a b -> List.eq (fun x y -> x == y) a b)
        feature_vectors in
    let totalvec = List.length feature_vectors in
    (* let _ = printf "\n" in
     * let _ = printf "set:%s\n" (F.layout_set feature_set) in
     * let _ = List.iter (fun fvec -> printf "fvec:%s\n" (boollist_to_string fvec))
     *     feature_vectors in *)
    let if_neg = ref false in
    let update v =
      match Hashtbl.find_opt pos v, Hashtbl.find_opt neg v with
      | None, None ->
        let _ = if_neg := true in
        (* let _ = printf "v:%s\n" (boollist_to_string v) in *)
        (* let _ = raise @@ InterExn "zz" in *)
        Hashtbl.add neg v iternum
      | _, _ -> ()
    in
    let _ = List.iter update feature_vectors in
    (* let _ = raise @@ InterExn "zz" in *)
    if_neg, totalvec

  let neg_update_opt ctx pos neg model feature_set dtnames chooses dt fv =
    let chooses = List.map (fun i -> SE.Literal (T.Int, SE.L.Int i)) chooses in
    (* let _ = printf "chooses:%s\n" (List.to_string SE.layout chooses) in
     * let _ = List.iter (fun dtname ->
     *     printf "%s = %i\n" dtname (S.get_int_name ctx model dtname)) dtnames in *)
    let counter_vecs =
      List.remove_duplicates (fun vec vec' ->
          List.eq (fun x y -> x == y) vec vec') @@
      List.map (fun m ->
          let exprs =
            List.map (fun feature ->
                Epr.to_z3 ctx @@ Epr.substm m @@ F.to_epr feature) feature_set in
          (* let _ = printf "p:%s\n" (List.to_string (fun e -> (Expr.to_string e)) exprs) in *)
          List.map (S.get_pred model) exprs) @@
      List.map (fun (dtname, intnames) ->
          List.fold_left (fun m ((_, name), e) ->
              StrMap.add name e m
            )
            (StrMap.add (snd dt)
               (SE.Literal (T.Int, SE.L.Int (S.get_int_name ctx model dtname)))
               StrMap.empty)
            (List.combine fv intnames)) @@
      List.cross
        dtnames (List.choose_n_eq (fun x y -> x == y) chooses (List.length fv)) in
    (* let _ = printf "len(vecs) = %i\n" (List.length vecs) in *)
    let neg_counter = ref 0 in
    let if_updated = ref false in
    let _ = List.iter (fun s ->
        match Hashtbl.find_opt pos s with
        | Some _ -> ()
        | None ->
          match Hashtbl.find_opt neg s with
          | Some _ -> ()
          | None -> if_updated := true; neg_counter := (!neg_counter) + 1;
            Hashtbl.add neg s ()
      ) counter_vecs
    in
    ()

  let infer ~ctx ~vc ~spectable ~preds ~bpreds ~startX ~maxX ~sampledata ~samplebound =
    let fv_num = startX in
    let _, vars = Ast.extract_variables vc in
    let unbounded_dts = List.filter (fun (tp, _) -> T.is_dt tp) vars in
    let dttp = match unbounded_dts with
      | [] -> raise @@ InterExn "no data type exists"
      | (tp, _) :: t ->
        if List.for_all (fun (tp', _) -> T.eq tp tp') t then tp else
          raise @@ UndefExn "axiom dttp"
    in
    let dt = dttp, "dt" in
    let fvints = List.filter_map (fun (tp, name) ->
        match tp with T.Int -> Some name | _ -> None) vars in
    let dttp, unbounded_dts = check_unbounded_dts unbounded_dts in
    let unbounded_ints, neg_vc_skolemized =
      Ast.skolemize @@ Ast.application (Ast.to_nnf (Ast.Not vc)) spectable in
    let unbounded_ints = unbounded_ints @ fvints in
    (* let _ = printf "unbounded_int(%i):%s\n" (List.length unbounded_ints)
     *     (StrList.to_string unbounded_ints) in *)
    (* let fv_num_max = List.length unbounded_ints in *)
    (* let _ = printf "unbounded_ints:%s\n" (StrList.to_string unbounded_ints) in
     * let _ = printf "unbounded_dts:%s\n" (StrList.to_string unbounded_dts) in *)
    let neg_vc_with_ax axiom =
      Boolean.mk_and ctx [
        Ast.to_z3 ctx (Ast.Not vc) spectable;
        Epr.forallformula_to_z3 ctx axiom] in
    let neg_vc_with_constraint range axiom =
      let constraints = interval ctx unbounded_ints range in
      (* let _ = printf "constraints = %s\n" (Expr.to_string constraints) in
       * let _ = printf "neg_vc_skolemized = %s\n"
       *     (Expr.to_string (Ast.to_z3 ctx neg_vc_skolemized spectable)) in *)
      Boolean.mk_and ctx [
        constraints;
        Ast.to_z3 ctx neg_vc_skolemized spectable;
        Epr.forallformula_to_z3 ctx axiom] in
    let pn_to_axiom_epr feature_set pos neg =
      let data = {FV.dfeature_set = feature_set;
                  FV.labeled_vecs =
                    Hashtbl.fold (fun vec _ vecs -> (true, vec) :: vecs) pos @@
                    Hashtbl.fold (fun vec _ vecs -> (false, vec) :: vecs) neg []} in
      D.classify data
    in
    let sampling fv_num axiom_epr feature_set dt fv chooses num =
      let samples = R.gen ~chooses:chooses ~num:num ~tp:dttp ~bound:samplebound in
      (* let _ = List.iter (fun s -> printf "[%s]\n" (V.layout s)) samples in *)
      let vecs =
        List.map (fun m ->
            List.map (fun feature -> F.exec feature m) feature_set) @@
        List.filter_map (fun m ->
            if Epr.exec axiom_epr m then None else Some m) @@
        List.map (fun (dtv, argsv) ->
            List.fold_left (fun m ((_, name), v) ->
                StrMap.add name v m
              ) (StrMap.add (snd dt) dtv StrMap.empty) (List.combine fv argsv)) @@
        List.cross samples (List.choose_n (List.map (fun i -> V.I i) chooses) fv_num) in
      vecs
    in
    let pos_update fv_num pos neg feature_set dt fv chooses num numiter =
      let oldpos = Hashtbl.length pos in
      let samplesize = ref 0 in
      let rec aux counter =
        let axiom_epr = Epr.simplify_ite @@ D.to_epr @@ pn_to_axiom_epr feature_set pos neg in
        (* let _ = printf "axiom_epr:%s\n" (Epr.layout axiom_epr) in *)
        let ps = sampling fv_num axiom_epr feature_set dt fv chooses num in
        let _ = samplesize := (!samplesize) + (List.length ps) in
        let ps = List.remove_duplicates (fun vec vec' ->
            List.eq (fun x y -> x == y) vec vec') ps in
        (* let _ = List.iter (fun vec -> printf "%s\n" (boollist_to_string vec)) ps in *)
        match ps with
        | [] -> counter
        | _ ->
          let _ = List.iter (fun s ->
              match Hashtbl.find_opt pos s with
              | Some _ -> ()
              | None -> Hashtbl.add pos s numiter) ps in
          let _ = List.iter (fun s ->
              match Hashtbl.find_opt neg s with
              | Some _ -> Hashtbl.remove neg s
              | None -> ()) ps in
          aux (counter + 1)
          (* () *)
      in
      let times = aux 0 in
      let newpos = (Hashtbl.length pos) - oldpos in
      {postimes = times; samplesize=(!samplesize); totalposvec = newpos}
    in
    let rec main_loop fv_num total_stat =
      (* let _ = printf "fv_num=%i\n" fv_num in *)
      if fv_num > maxX then total_stat, None else
        let fv = List.map (fun n -> (T.Int, n)) @@ List.init fv_num (fun i -> sprintf "u_%i" i) in
        (* let feature_set = F.make_set ([dt] @ fv) in *)
        let feature_set = F.make_set_from_preds preds bpreds dt fv in
        let _ = printf "set:%s\n" (F.layout_set feature_set) in
        (* let _ = raise @@ InterExn "zz" in *)
        let positives = Hashtbl.create 10000 in
        let negatives = Hashtbl.create 10000 in
        let rec main_loop_with_fixed_fv stat =
             (* {static_hyp; numIter;posSample;negSample;
              * poshypvec;neghypvec;} = *)
          (* let numIter = if numIter >= max_main_loop_with_fixed_fv_times then
           *     raise @@ InterExn "main_loop_with_fixed_fv: too many iterations"
           *   else numIter + 1 in *)
          let p_size, n_size = map_double Hashtbl.length (positives, negatives) in
          (* let _ = Printf.printf "p_size:%i n_size:%i\n" p_size n_size in *)
          let axiom =
            D.to_forallformula @@
            if (p_size == 0) && (n_size == 0) then D.T
            else pn_to_axiom_epr feature_set positives negatives in
          let valid, _ = S.check ctx (neg_vc_with_ax axiom) in
          if valid
          then (total_stat @ [stat]), Some (dttp, Epr.forallformula_simplify_ite axiom)
          else
            let rec limited_smt_check upper_bound =
              (* let _ = printf "upper_bound = %i\n" upper_bound in *)
              let range = (0, upper_bound) in
              let chooses = List.init ((List.length fv) + 1) (fun i -> i) in
              let _, m = S.check ctx (neg_vc_with_constraint range axiom) in
              match m with
              | None -> limited_smt_check (upper_bound + 1)
              | Some m -> chooses, m
            in
            let chooses, m = limited_smt_check (List.length fv) in
            (* let _ = printf "model:%s\n" (Model.to_string m) in *)
            (* let _ = neg_update_opt ctx positives negatives
             *     m feature_set unbounded_dts chooses dt fv in *)
            let _, totalvec = neg_update_raw2 ctx positives negatives
                m feature_set dt fv unbounded_dts stat.numIter in
            let negSample = stat.negSample @ [{posvec = 0; negvec = 0; totalvec = totalvec}] in
            (* let _ =
             *   printf "pos:\n";
             *   Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) positives;
             *   printf "neg:\n";
             *   Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) negatives in *)
            (* let _ = raise @@ InterExn "ZZ" in *)
            let pos_stat = pos_update fv_num positives negatives
                feature_set dt fv chooses sampledata stat.numIter in
            let posSample = stat.posSample @ [pos_stat] in
            (* let _ =
             *   printf "pos:\n";
             *   Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) positives;
             *   printf "neg:\n";
             *   Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) negatives in *)
            let negSample = update_negSample negSample stat.numIter negatives in
            if (Hashtbl.length positives == p_size) &&
               (Hashtbl.length negatives == n_size)
            then
              (* let _ = printf "raw\n" in *)
              (* if neg_update_raw ctx positives negatives m feature_set dt fv unbounded_dts
               * then
               *   let _ = pos_update fv_num positives negatives feature_set dt fv chooses 150 in
               *   main_loop_with_fixed_fv ()
               * else *)
              main_loop (fv_num + 1) (total_stat @ [stat])
            else
              main_loop_with_fixed_fv
                {static_hyp = stat.static_hyp; numIter = stat.numIter + 1;negSample;posSample;
                 poshypvec = Hashtbl.length positives;
                 neghypvec = Hashtbl.length negatives;}
        in
        main_loop_with_fixed_fv (make_stat_hyp fv_num feature_set)
    in
    let stats, res = main_loop fv_num [] in
    (* let _ = List.iter (fun stat -> printf "%s\n" (layout_stat_hyp stat)) stats in *)
    stats, res
end
