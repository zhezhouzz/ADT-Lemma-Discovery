module type AxiomSyn = sig
  module D: Dtree.Dtree
  module Ast = Language.SpecAst
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
  val axiom_infer: ctx:Z3.context -> vc:Ast.t -> spectable:Ast.spec Utils.StrMap.t -> Ast.E.forallformula
end

module AxiomSyn (D: Dtree.Dtree) (F: Ml.FastDT.FastDT) = struct
  module D = D
  module V = Preds.Pred.Value
  module P = Preds.Pred.Predicate
  module Ast = Language.SpecAst
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
    let additional =
      match IntList.max_opt fv with
      | None -> raise @@ InterExn "randomgen"
      | Some m -> m + 1
    in
    List.map (fun l -> V.L l) @@
    List.remove_duplicates IntList.eq @@
    List.choose_eq_all (fun a b -> a == b) (additional :: (fv @ fv))
  (* List.combination_l_all (additional :: (fv @ fv)) *)

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

  let fixed_sample ctx l =
    Boolean.mk_and ctx (
      List.fold_left (fun cs (name, dt) ->
          match dt with
          | V.I i ->
            (Epr.SE.fixed_int_to_z3 ctx name i):: cs
          | V.B _ -> cs
          | _ ->
            (Epr.SE.fixed_dt_to_z3 ctx "member" name dt)::
            (Epr.SE.fixed_dt_to_z3 ctx "list_order" name dt)::
            cs
        ) [] l
    )

  let sample_constraint ctx fv l (s, e) =
    let c = fixed_sample ctx l in
    let geE a b = Epr.Atom (Epr.SE.Op (Epr.SE.Bool, ">=", [a; b])) in
    let sz3, ez3 = map_double (fun x -> Epr.SE.Literal (Epr.SE.Int, Epr.SE.L.Int x)) (s, e) in
    let interval = Epr.to_z3 ctx
        (Epr.And (List.fold_left (fun l u -> l @ [geE u sz3; geE ez3 u]) [] fv)) in
    Boolean.mk_and ctx [interval;c]

  module SE = Epr.SE
  let sample_num = 2
  let start_size = 2
  open Printf

  let interval ctx exists_fv (s, e) =
    let (s', e') =
      map_double (fun x -> Epr.SE.Literal (Epr.SE.Int, Epr.SE.L.Int x)) (s, e) in
    let name_to_var name = SE.Var (SE.Int, name) in
    let geE a b = Epr.Atom (SE.Op (SE.Bool, ">=", [a; b])) in
    let interval = Epr.to_z3 ctx
        (Epr.And (List.fold_left (fun l u ->
             l @ [geE (name_to_var u) s'; geE e' (name_to_var u)]) [] exists_fv)) in
    interval

  let sample_constraint_over_dt ctx dtname l exists_fv (s, e) =
    let c = fixed_sample ctx l in
    let dt = SE.Var (SE.IntList, dtname) in
    let u, v = SE.Var (SE.Int, "u"), SE.Var (SE.Int, "v") in
    let s', e' = SE.Literal (SE.Int, SE.L.Int s), SE.Literal (SE.Int, SE.L.Int e) in
    let geE a b = Epr.Atom (SE.Op (SE.Bool, ">=", [a; b])) in
    let member l u = Epr.Atom (SE.Op (SE.Bool, "member", [l; u])) in
    let head l u = Epr.Atom (SE.Op (SE.Bool, "member", [l; u])) in
    let list_order l u v = Epr.Atom (SE.Op (SE.Bool, "list_order", [l; u; v])) in
    let dt_c = ["u"; "v"], Epr.And [
        Epr.Implies (
          Epr.Not (Epr.And [geE u s';geE e' u]),
          Epr.Not (Epr.Or [member dt u; head dt u]));
        Epr.Implies (
          Epr.Not (Epr.And [geE u s';geE e' u;geE v s';geE e' v]),
          Epr.Not (list_order dt u v));
      ] in
    let name_to_var name = SE.Var (SE.Int, name) in
    let interval = Epr.to_z3 ctx
        (Epr.And (List.fold_left (fun l u ->
             l @ [geE (name_to_var u) s'; geE e' (name_to_var u)]) [] exists_fv)) in
    Boolean.mk_and ctx [c; interval;
                        Epr.forallformula_to_z3 ctx dt_c;
                       ]

  let get_sat_conj ctx vc spec_tab =
    let vc_nnf = Ast.to_nnf vc in
    let vc_dnf = Ast.to_dnf (Ast.remove_unsat_clause vc_nnf) in
    let rec aux = function
      | [] -> []
      | h :: t -> if fst @@ S.check ctx (Ast.to_z3 ctx h spec_tab)
        then aux t
        else
          let _ = printf "conj:%s\n" (Ast.layout h) in
          (* let _ = printf "conj:%s\n" (Ast.layout (Ast.application h spec_tab)) in *)
          let fv, dts, skolemize_conj = Ast.skolemize_conj (Ast.application h spec_tab) in
          let _ = printf "fv=[%s] dts=[%s]\n" (List.to_string (fun x -> x) fv)
              (List.to_string (fun x -> x) dts) in
          (* let _ = printf "conj:%s\n" (Ast.layout skolemize_conj) in *)
          let valid, _ = S.check ctx (Ast.to_z3 ctx skolemize_conj spec_tab) in
          if valid then raise @@ InterExn "get_sat_conj" else
            (fv, dts, skolemize_conj, h) :: (aux t)
    in
    match vc_dnf with
    | Or ps -> aux ps
    | _ -> raise @@ InterExn "get_sat_conj"

  let complement s len default =
    let vecs = List.choose_n_eq (fun a b -> a == b) [true;false] len in
    let vecs = List.filter_map (fun vec ->
        match List.find_opt (fun s -> List.eq (fun a b -> a == b) s.vec vec) s with
        | None -> Some vec
        | Some _ -> None
      ) vecs in
    let negs = List.map (fun vec -> cex_to_sample default vec) vecs in
    negs

  let additional_axiom ctx =
    let module E = Ast.E in
    let list_var name = SE.Var (SE.IntList, name) in
    let int_var name = SE.Var (SE.Int, name) in
    let head l u = E.Atom (SE.Op (SE.Bool, "head", [l; u])) in
    let member l u = E.Atom (SE.Op (SE.Bool, "member", [l; u])) in
    let list_order l u v = E.Atom (SE.Op (SE.Bool, "list_order", [l; u; v])) in
    let l1    = list_var "l1" in
    let u    = int_var "u" in
    let v    = int_var "v" in
    let w    = int_var "w" in
    let axiom = (["l1"; "u"; "v"; "w"],
                 E.And [
                   (* E.Implies (list_order l1 u v, E.Not (head l1 v)); *)
                   E.Implies (head l1 u, member l1 u);
                   E.Implies (list_order l1 u v,
                              E.Or [E.And [head l1 u; member l1 v];
                                    E.And [head l1 w;list_order l1 w u]]);
                 ]
                ) in
    E.forallformula_to_z3 ctx axiom

  (* prevent loop forever *)
  let max_main_loop_times = 4

  let axiom_infer ~ctx ~vc ~spectable =
    (* TODO: handle interal integers... *)
    let _, vars = Ast.extract_variables vc in
    let dtnames = List.filter_map (fun (tp, name) ->
        if SE.is_dt tp then Some name else None) vars in
    let intnames = List.filter_map (fun (tp, name) ->
        match tp with
        | SE.Int -> Some name
        | _ -> None) vars in
    (* let _ = List.iter (fun name -> printf "var:%s\n" name) dtnames in *)
    let neg_vc_nnf = Ast.to_nnf (Ast.Not vc) in
    let neg_vc_nnf_applied = Ast.application neg_vc_nnf spectable in
    let exists_fv, neg_vc_skolemized = Ast.skolemize neg_vc_nnf_applied in
    (* let _ = printf "exists_fv:%s\nvc:%s\n"
     *     (List.to_string (fun x -> x) exists_fv) (Ast.layout neg_vc_skolemized) in *)
    let counter = ref max_main_loop_times in
    (* TODO: increase number of fv automatically... *)
    let fv_num = 2 in
    let title = make_title fv_num in
    let neg_vc_with_ax axiom =
      Boolean.mk_and ctx [
        additional_axiom ctx;
        Ast.to_z3 ctx neg_vc_skolemized spectable
        ; Epr.forallformula_to_z3 ctx axiom] in
    let rec main_loop positives negatives axiom =
      let _ =
        if (!counter) <= 0 then
          raise @@ InterExn "main_loop: too many iterations"
        else counter:= (!counter) - 1 in
      let valid, _ = S.check ctx (neg_vc_with_ax axiom) in
      if valid then axiom else
        let range = (0, 3) in
        let constraints = interval ctx (intnames @ exists_fv) range in
        let _, m = S.check ctx (Boolean.mk_and ctx [constraints; neg_vc_with_ax axiom]) in
        let m = match m with None -> raise @@ InterExn "bad range" | Some m -> m in
        let int_to_se i = SE.Literal (SE.Int, SE.L.Int i) in
        let get_interpretation ctx m title dtname args =
          let args = List.map int_to_se args in
          let title_b = List.map
              (fun feature -> D.feature_to_epr feature ~dtname:dtname ~fv:args) title in
          let title_z3 = List.map (fun b -> Epr.to_z3 ctx b) title_b in
          List.map (fun z -> S.get_pred m z) title_z3
        in
        let all_args = List.choose_n_eq (fun x y -> x == y) (IntList.of_range range) fv_num in
        let all_args_vec dtname =
          List.combine all_args
            (List.map (fun args -> get_interpretation ctx m title dtname args) all_args) in
        let all_args_vec = List.flatten (List.map all_args_vec dtnames) in
        (* let _ = printf "num:%i\n" (List.length all_args_vec) in *)
        let booll_eq vec vec' = List.eq (fun x y -> x == y) vec vec' in
        let all_args_vec = List.remove_duplicates
            (fun (_, vec) (_, vec') -> booll_eq vec vec') all_args_vec in
        let _ = List.iter
            (fun (args, vec) -> printf "%s:%s\n"
                (IntList.to_string args) (boollist_to_string vec)) all_args_vec in
        let mk_positives positives args =
          let dts = randomgen args in
          let samples = List.map
              (fun dt -> make_sample title dt (List.map (fun i -> V.I i) args)) dts in
          let positives = positives @ samples in
          List.remove_duplicates (fun p p' -> booll_eq p.vec p'.vec) positives
        in
        let update (positives, negatives) (args, vec) =
          let eq_that_vec p = booll_eq p.vec vec in
          match List.find_opt eq_that_vec positives with
          | Some _ -> positives, negatives
          | None ->
            let samples = mk_positives positives args in
            let positives =
              List.remove_duplicates (fun p p' -> booll_eq p.vec p'.vec) (samples @ positives)
            in
            match List.find_opt eq_that_vec samples with
            | Some _ -> positives, negatives
            | None ->
              positives, (cex_to_sample (List.map (fun i -> V.I i) args) vec) :: negatives
        in
        let positives, negatives =
          List.fold_left update (positives, negatives) all_args_vec in
        (* let _ = printf "title: %s\n" (layout_title title) in
         * let _ = List.iter (fun pos -> printf "pos:%s\n" (layout_sample pos)) positives in
         * let _ = List.iter (fun neg -> printf "neg:%s\n" (layout_sample neg)) negatives in *)
        let axiom = classify title ~pos:positives ~neg:negatives in
        let axiom = D.to_forallformula axiom ~dtname:"l" in
        let axiom = Epr.forallformula_simplify_ite axiom in
        (* let _ = printf "axiom:%s\n" (Epr.layout_forallformula axiom) in
         * let _ = printf "axiom:%s\n" (Expr.to_string (Epr.forallformula_to_z3 ctx axiom)) in *)
        main_loop positives negatives axiom
        (* raise @@ InterExn "zz" *)
    in
    main_loop [] [] ([], Epr.True)
end

module Syn = AxiomSyn(Dtree.Dtree)(Ml.FastDT.FastDT)
