module type RealSample = sig
  type value = Pred.Value.t
  type t = {names: (Tp.Tp.t * string) list;
            values: value list list}
  val append: t -> t -> t
end

module RealSample = struct
  type value = Pred.Value.t
  type t = {names: (Tp.Tp.t * string) list;
            values: value list list}
  open Utils
  let append s1 s2 =
    {names = s1.names @ s2.names;
     values = List.map (fun (a, b) -> a @ b) @@ List.cross s1.values s2.values}
end

module type FeatureVector = sig
  type t = {feature_set: Feature.Feature.set;
            vecs: bool list list}
  type data = {dfeature_set: Feature.Feature.set;
               labeled_vecs: (bool * (bool list)) list}
  type sides =
    | Single of data
    | Double of data * data
  val of_real_samples: Feature.Feature.set -> RealSample.t -> t
  val remove_field: t -> Feature.Feature.t -> t
  val get_field: t -> Feature.Feature.t -> bool list
  val split: t -> Feature.Feature.t -> sides
end

module FeatureVector = struct
  type t = {feature_set: Feature.Feature.set;
            vecs: bool list list}
  type data = {dfeature_set: Feature.Feature.set;
               labeled_vecs: (bool * (bool list)) list}
  type sides =
    | Single of data
    | Double of data * data
  module F = Feature.Feature
  open Utils
  open RealSample
  let of_real_samples feature_set {names; values} =
    let make_env names value = List.fold_left (fun m ((_, name), v) ->
        StrMap.add name v m
      ) StrMap.empty (List.combine names value) in
    let ss = List.map (fun value ->
        let m = make_env names value in
        List.map (fun feature -> F.exec feature m) feature_set) values in
    let hashtbl = Hashtbl.create (List.length ss) in
    let _ = List.iter (fun v ->
        match Hashtbl.find_opt hashtbl v with
        | Some _ -> ()
        | _ -> Hashtbl.add hashtbl v ()) ss in
    let vecs = Hashtbl.fold (fun v _ l -> v :: l) hashtbl [] in
    (* let vecs' = List.remove_duplicates (fun l1 l2 -> List.eq (fun x y -> x == y) l1 l2) ss in
     * let _ =
     *   if List.length vecs != List.length vecs'
     *   then Printf.printf "vecs: %i|%i|%i\n"
     *       (Hashtbl.length hashtbl) (List.length vecs) (List.length vecs')
     *   else () in *)
    {feature_set = feature_set;
     vecs = vecs}
  let remove_field {feature_set; vecs} target =
    let extract_feature = function
      | F.Pr (pred, [x], _) -> pred, x
      | F.Pr (_, _, _) -> raise @@ UndefExn "feature_vector_remove_field"
      | F.Eq (x, _) -> "==", x
      | F.Bo x -> "id", x
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
  let get_field {feature_set; vecs} feature =
    let i = List.lookup (fun f1 f2 -> F.eq f1 f2) feature feature_set in
    List.map (fun vec -> List.nth vec i) vecs

  type label = Pos | Neg | Unclear

  let label_eq = function
    | Pos, Pos -> true
    | Neg, Neg -> true
    | Unclear, Unclear -> true
    | _, _ -> false

  (* let split feature_vectors target =
   *   let y = get_field feature_vectors target in
   *   let feature_vectors = remove_field feature_vectors target in
   *   let bv_str_list = List.map BitVector.to_string feature_vectors.vecs in
   *   let bv_tbl = Hashtbl.create (List.length bv_str_list) in
   *   let _ = List.iter (fun (y, bv) ->
   *       match Hashtbl.find_opt bv_tbl bv with
   *       | Some Unclear -> ()
   *       | Some Pos -> if y then () else Hashtbl.replace bv_tbl bv Unclear
   *       | Some Neg -> if y then Hashtbl.replace bv_tbl bv Unclear else ()
   *       | None -> Hashtbl.add bv_tbl bv (if y then Pos else Neg)
   *     ) (List.combine y bv_str_list) in
   *   let by_value v =
   *     Hashtbl.fold (fun k v' r ->
   *         if label_eq (v, v')
   *         then (BitVector.of_string k) :: r
   *         else r) bv_tbl []
   *   in
   *   let pos, neg, unclear = by_value Pos, by_value Neg, by_value Unclear in
   *   let add_y y vecs = List.map (fun v -> (y, v)) vecs in
   *   if List.length unclear == 0
   *   then Single {dfeature_set = feature_vectors.feature_set;
   *                labeled_vecs = (add_y true pos) @ (add_y false neg)}
   *   else Double ({dfeature_set = feature_vectors.feature_set;
   *                 labeled_vecs = (add_y true (pos @ unclear)) @ (add_y false neg)},
   *                {dfeature_set = feature_vectors.feature_set;
   *                 labeled_vecs = (add_y true pos) @ (add_y false (neg @ unclear))}) *)

  let split feature_vectors target =
    let y = get_field feature_vectors target in
    let feature_vectors = remove_field feature_vectors target in
    let bv_tbl = Hashtbl.create (List.length feature_vectors.vecs) in
    let _ = List.iter (fun (y, bv) ->
        match Hashtbl.find_opt bv_tbl bv with
        | Some Unclear -> ()
        | Some Pos -> if y then () else Hashtbl.replace bv_tbl bv Unclear
        | Some Neg -> if y then Hashtbl.replace bv_tbl bv Unclear else ()
        | None -> Hashtbl.add bv_tbl bv (if y then Pos else Neg)
      ) (List.combine y feature_vectors.vecs) in
    let by_value v =
      Hashtbl.fold (fun k v' r ->
          if label_eq (v, v')
          then k :: r
          else r) bv_tbl []
    in
    let pos, neg, unclear = by_value Pos, by_value Neg, by_value Unclear in
    (* let dup = List.interset (fun l1 l2 -> List.eq (fun x y -> x == y) l1 l2) pos neg in
     * let _ = List.iter (fun l -> Printf.printf "%s\n" (boollist_to_string l)) dup in *)
    let add_y y vecs = List.map (fun v -> (y, v)) vecs in
    if List.length unclear == 0
    then Single {dfeature_set = feature_vectors.feature_set;
                 labeled_vecs = (add_y true pos) @ (add_y false neg)}
    else Double ({dfeature_set = feature_vectors.feature_set;
                  labeled_vecs = (add_y true (pos @ unclear)) @ (add_y false neg)},
                 {dfeature_set = feature_vectors.feature_set;
                  labeled_vecs = (add_y true pos) @ (add_y false (neg @ unclear))})
end
