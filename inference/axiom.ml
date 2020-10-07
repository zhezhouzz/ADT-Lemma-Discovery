module type AxiomSyn = sig
  val infer:
    ctx:Z3.context ->
    vc:Language.SpecAst.t ->
    spectable:Language.SpecAst.spec Utils.StrMap.t ->
    Language.SpecAst.E.forallformula
end

module AxiomSyn (D: Dtree.Dtree) = struct
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
  type vec = bool list
  type value = Pred.Value.t
  type typed_var = (Tp.Tp.t * string)
  open Z3

  let max_main_loop_times = 20

  let counter = ref max_main_loop_times

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

  let infer ~ctx ~vc ~spectable =
    let fv_num = 2 in
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
    let get_from_model model feature_set dtnames chooses dt fv =
      let chooses = List.map (fun i -> SE.Literal (T.Int, SE.L.Int i)) chooses in
      (* let _ = printf "chooses:%s\n" (List.to_string SE.layout chooses) in
       * let _ = List.iter (fun dtname ->
       *     printf "%s = %i\n" dtname (S.get_int_name ctx model dtname)) dtnames in *)
      let vecs =
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
      vecs
    in
    let neg_update pos neg counter_vecs =
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
      (* let _ = List.iter (fun vec -> printf "%s\n" (boollist_to_string vec)) counter_vecs in *)
      (* printf "neg_update:%i\n" (!neg_counter); *)
      ()
    in
    let pn_to_axiom_epr feature_set pos neg =
      let data = {FV.dfeature_set = feature_set;
                  FV.labeled_vecs =
                    Hashtbl.fold (fun vec _ vecs -> (true, vec) :: vecs) pos @@
                    Hashtbl.fold (fun vec _ vecs -> (false, vec) :: vecs) neg []} in
      D.classify data
    in
    let sampling axiom_epr feature_set dt fv chooses num =
      let samples = R.gen ~chooses:chooses ~num:num ~tp:dttp in
      (* let _ = List.iter (fun s -> printf "[%s]\n" (V.layout s)) samples in *)
      let vecs =
        List.remove_duplicates (fun vec vec' ->
            List.eq (fun x y -> x == y) vec vec') @@
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
    let pos_update pos neg feature_set dt fv chooses num =
      let rec aux () =
        let axiom_epr = Epr.simplify_ite @@ D.to_epr @@ pn_to_axiom_epr feature_set pos neg in
        (* let _ = printf "axiom_epr:%s\n" (Epr.layout axiom_epr) in *)
        let ps = sampling axiom_epr feature_set dt fv chooses num in
        (* let _ = List.iter (fun vec -> printf "%s\n" (boollist_to_string vec)) ps in *)
        match ps with
        | [] -> ()
        | _ ->
          let _ = List.iter (fun s ->
              match Hashtbl.find_opt pos s with
              | Some _ -> ()
              | None -> Hashtbl.add pos s ()) ps in
          let _ = List.iter (fun s ->
              match Hashtbl.find_opt neg s with
              | Some _ -> Hashtbl.remove neg s
              | None -> ()) ps in
          aux ()
          (* () *)
      in
      aux ()
    in
    let fv = List.map (fun n -> (T.Int, n)) @@ List.init fv_num (fun i -> sprintf "u_%i" i) in
    let feature_set = F.make_set ([dt] @ fv) in
    (* let _ = printf "set:%s\n" (F.layout_set feature_set) in *)
    let positives = Hashtbl.create 1000 in
    let negatives = Hashtbl.create 1000 in
    let rec main_loop () =
      let _ = if (!counter) <= 0 then
          raise @@ InterExn "main_loop: too many iterations"
        else counter:= (!counter) - 1 in
      let p_size, n_size = map_double Hashtbl.length (positives, negatives) in
      (* let _ = Printf.printf "p_size:%i n_size:%i\n" p_size n_size in *)
      let axiom =
        D.to_forallformula @@
        if (p_size == 0) && (n_size == 0) then D.T
        else pn_to_axiom_epr feature_set positives negatives in
      let valid, _ = S.check ctx (neg_vc_with_ax axiom) in
      if valid then axiom else
        let range = (0, (List.length fv)) in
        let chooses = List.init ((List.length fv) + 1) (fun i -> i) in
        let _, m = S.check ctx (neg_vc_with_constraint range axiom) in
        let m = match m with None -> raise @@ InterExn "bad range" | Some m -> m in
        (* let _ = printf "model:%s\n" (Model.to_string m) in *)
        let counter_vecs = get_from_model m feature_set unbounded_dts chooses dt fv in
        (* let _ = List.iter (fun vec -> printf "%s\n" (boollist_to_string vec)) counter_vecs in *)
        let _ = neg_update positives negatives counter_vecs in
        (* let _ =
         *   printf "pos:\n";
         *   Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) positives;
         *   printf "neg:\n";
         *   Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) negatives in *)
        let _ = pos_update positives negatives feature_set dt fv chooses 10 in
        (* let _ =
         *   printf "pos:\n";
         *   Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) positives;
         *   printf "neg:\n";
         *   Hashtbl.iter (fun vec _ -> printf "%s\n" (boollist_to_string vec)) negatives in *)
        if (Hashtbl.length positives == p_size) &&
           (Hashtbl.length negatives == n_size)
        then raise @@ InterExn "bad fv num"
        else
          main_loop ()
    in
    let axiom = main_loop () in
    let axiom = Epr.forallformula_simplify_ite axiom in
    (* let _ = printf "axiom:%s\n" (Epr.layout_forallformula axiom) in
     * let _ = printf "axiom:%s\n" (Expr.to_string (Epr.forallformula_to_z3 ctx axiom)) in *)
    axiom
end
