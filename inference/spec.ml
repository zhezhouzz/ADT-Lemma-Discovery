module type SpecSyn = sig
  module D: Dtree.Dtree
  module Ast = Language.SpecAst
  type vec = bool list
  type value = Pred.Value.t
  type typed_var = (Tp.Tp.t * string)
  type samples =
    | RealData of {names: typed_var list;
                   values: value list list}
    | FeatureVector of {feature_set: Feature.Feature.set;
                        vecs: vec list}
  val infer: ctx:Z3.context -> progtp:(typed_var list * typed_var list) -> prog:(value list -> value list) -> Ast.spec
end

module AxiomSyn (D: Dtree.Dtree) = struct
  module D = D
  module V = Pred.Value
  module P = Pred.Pred
  module Ast = Language.SpecAst
  module Epr = Ast.E
  module T = Tp.Tp
  module F = Feature.Feature
  module R = Randomgen.Randomgen
  module FastDT = Ml.FastDT.FastDT
  open Utils
  open Printf
  type vec = bool list
  type value = Pred.Value.t
  type typed_var = (Tp.Tp.t * string)
  type real_samples = {names: (Tp.Tp.t * string) list;
                       values: value list list}
  type feature_vectors = {feature_set: Feature.Feature.set;
                          vecs: vec list}

  let new_fv_name n =
    List.init n (fun i -> sprintf "u_%i" i)

  let simulate prog inptps outptps inps =
    let values = List.filter_map (fun inp ->
        try Some (inp @ (prog inp)) with InterExn _ -> None) inps in
    {names = inptps @ outptps; values = values}

  let sample_elim_universal (samples:real_samples) fv chooses =
    let fv_values =
      List.map (fun fv -> List.map (fun x -> V.I x) fv) @@
      List.choose_n_eq (fun x y -> x == y) chooses (List.length fv)
    in
    let values = List.map (fun (a, b) -> a @ b) @@ List.cross samples.values fv_values in
    {names = samples.names @ fv; values = values}

  let real_samples_append s1 s2 =
    {names = s1.names @ s2.names;
     values = List.map (fun (a, b) -> a @ b) @@ List.cross s1.values s2.values}

  let samples_to_vector feature_set {names; values} =
    let make_env names value = List.fold_left (fun m ((_, name), v) ->
        StrMap.add name v m
      ) StrMap.empty (List.combine names value) in
    {feature_set = feature_set;
     vecs = List.map (fun value ->
         let m = make_env names value in
         List.map (fun feature -> F.exec feature m) feature_set) values
    }

  let feature_vector_remove_field {feature_set; vecs} target =
    let extract_feature = function
      | F.Pr (pred, [x], _) -> pred, x
      | F.Pr (_, _, _) -> raise @@ UndefExn "feature_vector_remove_field"
      | F.Eq (x, _) -> "==", x
    in
    let farr = Array.of_list feature_set in
    let op, x = extract_feature target in
    let indicator = Array.init (Array.length farr) (fun i ->
        let op', x' = extract_feature farr.(i) in
        (String.equal op op') && (x == x')
      ) in
    let feature_set' = List.filter_mapi (fun i feature ->
        if indicator.(i) then None else Some feature
      ) feature_set in
    let vecs' =
      List.map (fun vec ->
          List.filter_mapi (fun i b ->
              if indicator.(i) then None else Some b
            ) vec) vecs in
    {feature_set = feature_set'; vecs = vecs'}
  let feature_vector_get_field {feature_set; vecs} feature =
    let i = List.lookup (fun f1 f2 -> F.eq f1 f2) feature feature_set in
    List.map (fun vec -> List.nth vec i) vecs

  type label = Pos | Neg | Unclear

  let label_eq = function
    | Pos, Pos -> true
    | Neg, Neg -> true
    | Unclear, Unclear -> true
    | _, _ -> false

  type data = {dfeature_set: F.set;
               labeled_vecs: (bool * (bool list)) list}
  type sides =
    | Single of data
    | Double of data * data

  let feature_vector_split feature_vectors target =
    let feature_vectors = feature_vector_remove_field feature_vectors target in
    let y = feature_vector_get_field feature_vectors target in
    let bv_str_list = List.map BitVector.to_string feature_vectors.vecs in
    let bv_tbl = Hashtbl.create (List.length bv_str_list) in
    let _ = List.iter (fun (y, bv) ->
        match Hashtbl.find_opt bv_tbl bv, y with
        | Some Unclear, _ -> ()
        | Some Pos, false -> Hashtbl.add bv_tbl bv Unclear
        | Some Pos, _ -> ()
        | Some Neg, true -> Hashtbl.add bv_tbl bv Unclear
        | Some Neg, _ -> ()
        | None, y -> Hashtbl.add bv_tbl bv (if y then Pos else Neg)
      ) (List.combine y bv_str_list) in
    let by_value v =
      Hashtbl.fold (fun k v' r ->
          if label_eq (v, v')
          then (BitVector.of_string k) :: r
          else r) bv_tbl []
    in
    let pos, neg, unclear = by_value Pos, by_value Neg, by_value Unclear in
    let add_y y vecs = List.map (fun v -> (y, v)) vecs in
    if List.length unclear == 0
    then Single {dfeature_set = feature_vectors.feature_set;
                 labeled_vecs = (add_y true pos) @ (add_y false neg)}
    else Double ({dfeature_set = feature_vectors.feature_set;
                  labeled_vecs = (add_y true (pos @ unclear)) @ (add_y false neg)},
                 {dfeature_set = feature_vectors.feature_set;
                  labeled_vecs = (add_y true pos) @ (add_y false (neg @ unclear))})

  let classify {dfeature_set;labeled_vecs} =
    let samples = List.map (fun (a, b) -> a, Array.of_list b) labeled_vecs in
    let dt = FastDT.make_dt ~samples:(Array.of_list samples) ~max_d:10 in
    let _ = FastDT.print_tree' dt in
    D.of_fastdt dt dfeature_set

  let infer ~progtp ~prog =
    let fv_num = 2 in
    let fv = List.map (fun n -> (T.Int, n)) @@ new_fv_name fv_num in
    let inptps, outptps = progtp in
    let feature_set = F.make_set (inptps @ outptps @ fv) in
    (* let inptps, outptps, fv_idxs = make_spec_var_assign progtp fv_num in
     * let args = (List.filter_map
     *               (fun (tp, idx) -> match tp with
     *                  | T.Int -> Some idx
     *                  | _ -> None
     *               ) (inptps @ outptps)) @ fv_idxs in
     * let spec_title = outp_title @ inp_title @ inner_title in *)
    let targets = List.fold_left (fun r dt -> r @ (F.make_target dt fv)) [] outptps in
    let _ = printf "targets = %s\n" (F.layout_set targets) in
    let chooses, inps = R.gen_tpvars ~tpvars:inptps ~num:10 ~fv_num:fv_num in
    let samples = simulate prog inptps outptps inps in
    let fv_samples =
      {names = fv;
        values = List.map (fun fv -> List.map (fun x -> V.I x) fv) @@
          List.choose_n_eq (fun x y -> x == y) chooses (List.length fv)} in
    (* let _ = List.iter (fun fv -> printf "fv:%s\n" (List.to_string V.layout fv)) fv_samples in *)
    let samples = real_samples_append samples fv_samples in
    let feature_vectors = samples_to_vector feature_set samples in
    (* let _ = List.iter (fun vec ->
     *     printf "%s\n" (boollist_to_string vec)
     *   ) vecs in *)
    let make_spec target =
      let one_side data =
        Epr.simplify_ite @@ D.to_epr (classify data) in
      let target_expr = F.to_epr target in
      match feature_vector_split feature_vectors target with
      | Single vecs' ->
        Epr.Iff (target_expr, one_side vecs')
      | Double (l, r) ->
        Epr.And [
          Epr.Implies (target_expr, one_side l);
          Epr.Implies (one_side r, target_expr);
        ]
    in
    let get_tpvar_name (_, name) = name in
    let spec = Epr.And (List.map (fun target -> make_spec target) targets) in
    let spec = List.map get_tpvar_name (inptps @ outptps),
               (List.map get_tpvar_name fv, spec) in
    let _ = printf "spec:%s\n" (Ast.layout_spec spec) in
    [], ([],Epr.True)
end
