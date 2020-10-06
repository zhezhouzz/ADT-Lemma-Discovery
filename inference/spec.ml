module type SpecSyn = sig
  type value = Pred.Value.t
  val infer: ctx:Z3.context -> progtp:(Tp.Tp.t list * Tp.Tp.t list) -> prog:(value list -> value list) -> Language.SpecAst.spec
end

module SpecSyn (D: Dtree.Dtree) = struct
  module D = D
  module V = Pred.Value
  module P = Pred.Pred
  module Ast = Language.SpecAst
  module Epr = Ast.E
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

  let new_fv_name n=
    List.init n (fun i -> sprintf "u_%i" i)

  let simulate prog inptps outptps inps =
    let values = List.filter_map (fun inp ->
        try Some (inp @ (prog inp)) with InterExn _ -> None) inps in
    {RS.names = inptps @ outptps; RS.values = values}

  let make_name tp =
    let name =
      match tp with
      | T.Int -> Renaming.unique "x"
      | T.IntList -> Renaming.unique "l"
      | T.IntTree | T.IntTreeI | T.IntTreeB -> Renaming.unique "tr"
      | T.Bool -> Renaming.unique "b"
    in
    tp, name

  let inp_limit num l =
    if List.length l > num then List.sublist l (0, num) else l

  let infer ~progtp ~prog =
    let fv_num = 2 in
    let fv = List.map (fun n -> (T.Int, n)) @@ new_fv_name fv_num in
    let inptps, outptps = progtp in
    let inptps = List.map make_name inptps in
    let outptps = List.map make_name outptps in
    let _ = List.iter (fun (_, name) -> printf "%s\n" name) inptps in
    (* let feature_set = F.make_set (outptps @ inptps @ fv) in *)
    let feature_set = F.make_set (inptps @ outptps @ fv) in
    let _ = printf "feature_set = %s\n" (F.layout_set feature_set) in
    let targets = List.fold_left (fun r dt -> r @ (F.make_target dt fv)) [] outptps in
    let _ = printf "targets = %s\n" (F.layout_set targets) in
    let chooses, inps = R.gen_tpvars ~tpvars:inptps ~num:12 ~fv_num:fv_num in
    let inps = inp_limit 150 inps in
    let _ = printf "inp:%i\n" (List.length inps) in
    (* let _ = raise @@ InterExn "bad" in *)
    (* let _ = List.iter (fun vs -> printf "%s\n" (List.to_string V.layout vs)) inps in *)
    let samples = simulate prog inptps outptps inps in
    (* let _ = Printf.printf "samples\n" in
     * let _ = List.iter (fun vs -> printf "%s\n" (List.to_string V.layout vs))
     *     samples.values in *)
    let fv_samples =
      {RS.names = fv;
       RS.values = List.map (fun fv -> List.map (fun x -> V.I x) fv) @@
         List.choose_n_eq (fun x y -> x == y) chooses (List.length fv)} in
    (* let _ = Printf.printf "fv_samples\n" in
     * let _ = List.iter (fun vs -> printf "%s\n" (List.to_string V.layout vs))
     *     fv_samples.values in *)
    let samples = RS.append samples fv_samples in
    (* let _ = Printf.printf "samples\n" in
     * let _ = List.iter (fun vs -> printf "%s\n" (List.to_string V.layout vs))
     *     samples.values in *)
    let feature_vectors = FV.of_real_samples feature_set samples in
    (* let _ = Printf.printf "of_real_samples\n" in
     * let _ = List.iter (fun vec ->
     *     printf "%s\n" (boollist_to_string vec)
     *   ) feature_vectors.vecs in
     * let _ = Printf.printf "of_real_samples\n" in *)
    let make_spec target =
      let one_side data =
        Epr.simplify_ite @@ D.to_epr (D.classify data) in
      let target_expr = F.to_epr target in
      match FV.split feature_vectors target with
      | Single vecs' ->
        (match target with
         | Bo _ -> one_side vecs'
         | _ -> Epr.Iff (target_expr, one_side vecs'))
      | Double (l, r) ->
        (match target with
         | Bo _ -> Epr.And [one_side l; Epr.Not (one_side r)]
         | _ ->
           Epr.And [
             Epr.Implies (target_expr, one_side l);
             Epr.Implies (one_side r, target_expr);
           ])
    in
    let get_tpvar_name (_, name) = name in
    let spec = Epr.And (List.map (fun target ->
        make_spec target
      ) targets) in
    let spec =
      let body = List.map get_tpvar_name fv, spec in
      match outptps with
      | [(T.Bool, _)] -> List.map get_tpvar_name inptps, body
      | _ ->
        List.map get_tpvar_name (inptps @ outptps), body in
    let _ = printf "spec:%s\n" (Ast.layout_spec spec) in
    spec
end
