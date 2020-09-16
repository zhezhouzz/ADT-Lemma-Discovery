module type AxiomSyn = sig
  module D: Dtree.Dtree
  module Ast = Language.Ast.SpecAst
  type vec = bool list
  type value = Preds.Pred.Value.t
  type sample = {dt: value; args: value list; vec: vec}
  type title = D.feature list
  val layout_title: title -> string
  val make_title: int -> title
  val make_sample: title -> value -> value list -> sample
  val cex_to_sample: value list -> vec -> sample
  val layout_sample: sample -> string
  val classify: title -> pos: sample list -> neg: sample list -> D.t
  val randomgen: int list -> value list
  val sample_constraint: Z3.context ->
    Ast.E.SE.t list -> (string * value) list -> (int * int) -> Z3.Expr.expr
  val axiom_infer: ctx:Z3.context -> vc:Ast.t -> spectable:Ast.spec Utils.StrMap.t -> prog:(value list -> (string * value) list) -> Ast.E.forallformula
end

module AxiomSyn (D: Dtree.Dtree) (F: Ml.FastDT.FastDT) = struct
  module D = D
  module V = Preds.Pred.Value
  module P = Preds.Pred.Predicate
  module Ast = Language.Ast.SpecAst
  module Epr = Ast.E
  module S = Solver
  open Utils
  open Printf
  type vec = bool list
  type sample = {dt: V.t; args: V.t list; vec: vec}
  type title = D.feature list

  let make_title fvs_num =
    let aux info =
      let _ = printf "%s(arglen = %i)\n" info.P.name info.P.num_int in
      let fvs_c = List.combination fvs_num info.P.num_int in
      let fvs_c =
        if info.P.permu then
        List.concat (List.map (fun l -> List.permutation l) fvs_c)
        else fvs_c
      in
      List.map (fun fv_c -> (info.P.name, fv_c)) fvs_c
    in
    List.fold_left (fun r info -> r @ (aux info)) [] P.preds_info

  let layout_title (title: title) =
    List.fold_left (fun r pred -> sprintf "%s [%s]" r (D.layout_feature pred)) "" title

  let randomgen (fv: int list) =
    List.map (fun l -> V.L l) @@
    List.remove_duplicates IntList.eq @@ List.combination_l_all (fv @ fv)

  let make_sample (title:title) (dt: V.t) (args: V.t list) =
    let vec = List.map (fun feature -> D.exec_feature feature dt args) title in
    {dt; args; vec}

  let cex_to_sample (args: V.t list) (vec: bool list) =
    {dt = V.NotADt; args; vec}

  let layout_sample {dt; args; vec} =
    sprintf "%s(%s) [%s]" (V.layout dt) (List.to_string V.layout args) (boollist_to_string vec)

  let classify_ (title: title) (_:vec list) (_:vec list) : D.t =
    let member0 = List.nth title 0 in
    let ord = List.nth title 2 in
    D.Node (ord, D.Leaf member0, D.T)

  let dt_to_dt title dt =
    let rec aux = function
      | F.Leaf {c_t; c_f} ->
        if (Float.abs c_t) < 1e-3 then D.F
        else if (Float.abs c_f) < 1e-3 then D.T
        else raise @@ InterExn (sprintf "Bad Dt Result(%f, %f)" c_t c_f)
      | F.Node ({split;if_t;if_f}) ->
        match List.nth_opt title split with
        | None -> raise @@ InterExn "Bad Dt Result"
        | Some p -> D.Node (p, aux if_t, aux if_f)
    in
    aux dt

  let classify title ~pos ~neg =
    let pos = List.map (fun s -> true, Array.of_list s.vec) pos in
    let neg = List.map (fun s -> false, Array.of_list s.vec) neg in
    let dt = F.make_dt ~samples:(Array.of_list (pos @ neg)) ~max_d:10 in
    let _ = F.print_tree' dt in
    dt_to_dt title dt

  open Z3

  let sample_constraint ctx fv l (s, e) =
    let c = Boolean.mk_and ctx (
        List.fold_left (fun cs (dtname, dt) ->
            match dt with
            | V.I _ | V.B _ -> cs
            | _ ->
              (Epr.SE.fixed_dt_to_z3 ctx "member" dtname dt)::
              (Epr.SE.fixed_dt_to_z3 ctx "list_order" dtname dt)::
              cs
          ) [] l
      ) in
    let geE a b = Epr.Atom (Epr.SE.Op (Epr.SE.Bool, ">=", [a; b])) in
    let sz3, ez3 = map_double (fun x -> Epr.SE.Literal (Epr.SE.Int, Epr.SE.L.Int x)) (s, e) in
    let interval = Epr.to_z3 ctx
        (Epr.And (List.fold_left (fun l u -> l @ [geE u sz3; geE ez3 u]) [] fv)) in
    Boolean.mk_and ctx [interval;c]
  module SE = Epr.SE
  let sample_num = 2
  let start_size = 2
  open Printf
  let axiom_infer ~ctx ~vc ~spectable ~prog =
    let rintg = QCheck.Gen.int_range 0 start_size in
    let gens = [QCheck.Gen.(map (fun x -> V.I x) rintg);  QCheck.Gen.((map (fun x -> V.L x) (small_list rintg)))] in
    let samples = List.map (fun gen -> QCheck.Gen.generate ~n:sample_num gen) gens in
    let samples = List.shape_reverse samples in
    let _ = List.iter (fun l -> printf "{%s}\n" (List.to_string V.layout l)) samples in
    (* let interp = prog [V.I 2; V.L []] in *)
    let interp = prog (List.nth samples 0) in
    (* let _ = List.iter (fun (name, v) -> printf "%s:%s\n" name (V.layout v)) interp in *)
    let negfv, negvc = Ast.neg_to_z3 ctx vc spectable in
    let rec aux positives negatives axiom =
      let neg_vc_with_ax =
        Boolean.mk_and ctx [negvc; Epr.forallformula_to_z3 ctx axiom] in
      let valid, _ = S.check ctx neg_vc_with_ax in
      if valid then axiom else
        let cs, (dtname, _) = List.match_snoc interp in
        let negfv = List.map (fun u -> SE.Var (SE.Int, u)) negfv in
        let range = IntList.bigger_range @@ V.flatten_forall_l @@ snd @@ List.split interp in
        let _ = printf "range = (%i, %i)\n" (fst range) (snd range) in
        let constraints = sample_constraint ctx negfv cs range in
        let neg_vc_fixed_dt = Boolean.mk_and ctx [constraints; negvc] in
        let _, m = S.check ctx neg_vc_fixed_dt in
        let m = match m with None -> raise @@ InterExn "axiom_infer::bad" | Some m -> m in
        let get_interpretation ctx m title fv =
          let title_b = List.map
              (fun feature -> D.feature_to_epr feature ~dtname:dtname ~fv:fv) title in
          let title_z3 = List.map (fun b -> Epr.to_z3 ctx b) title_b in
          List.map (fun fv -> S.get_int m (SE.to_z3 ctx fv)) fv,
          List.map (fun z -> S.get_pred m z) title_z3
        in
        let title = make_title (List.length negfv) in
        let fvv, predv = get_interpretation ctx m title negfv in
        let dts = randomgen fvv in
        let fvv_exp = List.map (fun x -> V.I x) fvv in
        let positives = positives @ (List.map (fun dt -> make_sample title dt fvv_exp) dts) in
        let negatives = (cex_to_sample fvv_exp predv) :: negatives in
        let axiom = classify title ~pos:positives ~neg:negatives in
        let axiom = D.to_forallformula axiom ~dtname:"l" in
        aux positives negatives axiom
    in
    aux [] [] ([], Epr.True)
end

module Syn = AxiomSyn(Dtree.Dtree)(Ml.FastDT.FastDT)
