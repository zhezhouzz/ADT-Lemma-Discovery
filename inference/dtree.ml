module type Dtree = sig
  type value = Pred.Value.t
  type feature = Feature.Feature.t
  type feature_set = Feature.Feature.set
  type label = Pos | Neg | MayNeg
  type 'a t =
    | T
    | F
    | Leaf of 'a
    | Node of 'a * 'a t * 'a t
  val exec: feature t -> value Utils.StrMap.t -> bool
  val exec_vector: feature t -> feature_set -> bool list -> bool
  val exec_vector_idx: int t -> bool list -> bool
  val layout: feature t -> string
  val to_epr: feature t -> Language.SpecAst.E.t
  val to_epr_idx: int t -> Language.SpecAst.E.t list -> Language.SpecAst.E.t
  val to_forallformula: feature t -> Language.SpecAst.E.forallformula
  val to_spec: feature t -> Language.SpecAst.spec
  val of_fastdt: Ml.FastDT.FastDT.dt -> feature_set -> feature t
  val classify: Sample.FeatureVector.data -> feature t
  val classify_hash: feature_set ->
    (bool list, 'a) Hashtbl.t -> ('a -> bool) -> feature t * int t
  val merge_dt: feature_set -> int t -> int t -> feature t * int t
  val subtract_dt: feature_set -> int t -> int t -> feature t * int t
  val len: feature t -> int
  val dt_summary: feature t -> feature_set -> (int * int)
  val layout_label: label -> string
  val is_pos: label -> bool
end

module Dtree : Dtree = struct
  module Epr = Language.SpecAst.E
  module P = Pred.Pred
  module T = Tp.Tp
  module F = Feature.Feature
  module FV = Sample.FeatureVector
  module FastDT = Ml.FastDT.FastDT
  open Utils
  open Printf
  type value = Pred.Value.t
  type feature = Feature.Feature.t
  type feature_set = feature list
  type label = Pos | Neg | MayNeg
  type 'a t =
    | T
    | F
    | Leaf of 'a
    | Node of 'a * 'a t * 'a t

  let layout_label = function
    | Pos -> "pos"
    | Neg -> "neg"
    | MayNeg -> "mayneg"

  let exec (dt: feature t) m : bool =
    let rec aux = function
      | T -> true
      | F -> false
      | Leaf feature -> F.exec feature m
      | Node (feature, l, r) ->
        if F.exec feature m then aux l else aux r
    in
    aux dt

  let exec_vector (dt: feature t) (fl: feature list) (vec: bool list) : bool =
    let m = List.combine fl vec in
    let get_b f = snd @@ List.find "exec_raw" (fun (f', _) -> F.eq f f') m in
    let rec aux = function
      | T -> true
      | F -> false
      | Leaf feature -> get_b feature
      | Node (feature, l, r) ->
        if get_b feature then aux l else aux r
    in
    aux dt

  let exec_vector_idx (dt: int t) (vec: bool list) : bool =
    let nth i = match List.nth_opt vec i with
      | None -> raise @@ InterExn "exec_vector_idx"
      | Some b -> b
    in
    let rec aux = function
      | T -> true
      | F -> false
      | Leaf feature -> nth feature
      | Node (feature, l, r) ->
        if nth feature then aux l else aux r
    in
    aux dt

  let rec layout = function
    | T -> "⊤"
    | F -> "⊥"
    | Leaf feature -> F.layout feature
    | Node (feature, l, r) ->
      sprintf "[%s](%s,%s)" (F.layout feature) (layout l) (layout r)

  let get_vars (dtree: feature t) =
    let rec aux = function
      | T | F -> [], []
      | Leaf feature -> F.get_vars feature
      | Node (feature, l, r) ->
        let dts, elems = F.get_vars feature in
        let (dts', elems'), (dts'', elems'') = map_double aux (l, r) in
        dts @ dts' @ dts'', elems @ elems' @ elems''
    in
    map_double List.remove_duplicates_eq (aux dtree)

  let to_epr dtree =
    let rec aux = function
      | T -> Epr.True
      | F -> Epr.Not Epr.True
      | Leaf feature -> F.to_epr feature
      | Node (feature, l, r) -> Epr.Ite (F.to_epr feature, aux l, aux r)
    in
    aux dtree

  let to_epr_idx dtree vars =
    let nth i = match List.nth_opt vars i with
      | None -> raise @@ InterExn "to_epr_idx"
      | Some b -> b
    in
    let rec aux = function
      | T -> Epr.True
      | F -> Epr.Not Epr.True
      | Leaf feature -> nth feature
      | Node (feature, l, r) -> Epr.Ite (nth feature, aux l, aux r)
    in
    aux dtree

  (* TODO: handle types in predicates *)
  let to_forallformula (dtree: feature t) =
    let dts, elems = get_vars dtree in
    let vars = List.map (fun v -> T.Int, v) (dts @ elems) in
    vars, to_epr dtree

  let to_spec (dtree: feature t) =
    let dts, elems = get_vars dtree in
    let dts = List.map (fun v -> T.Int, v) dts in
    let elems = List.map (fun v -> T.Int, v) elems in
    dts, (elems, to_epr dtree)


  let of_fastdt dt feature_set =
    let rec aux = function
      | FastDT.Leaf {c_t; c_f} ->
        let res =
          if (Float.abs c_t) < 1e-3 then F
          else if (Float.abs c_f) < 1e-3 then T
          else raise @@ InterExn (sprintf "Bad Dt Result(%f, %f)" c_t c_f)
        in
        (* let _ = Printf.printf "leaf(%f,%f) ->(%f,%f,%f) = %s\n" c_t c_f
         *     (Float.abs c_t) (Float.abs c_f) (1e-3) (layout res) in *)
        res
      | FastDT.Node ({split;if_t;if_f}) ->
        match List.nth_opt feature_set split with
        | None -> raise @@ InterExn "Bad Dt Result"
        | Some p -> Node (p, aux if_t, aux if_f)
    in
    aux dt

  let of_fastdt_idx dt =
    let rec aux = function
      | FastDT.Leaf {c_t; c_f} ->
        let res =
          if (Float.abs c_t) < 1e-3 then F
          else if (Float.abs c_f) < 1e-3 then T
          else raise @@ InterExn (sprintf "Bad Dt Result(%f, %f)" c_t c_f)
        in
        (* let _ = Printf.printf "leaf(%f,%f) ->(%f,%f,%f) = %s\n" c_t c_f
         *     (Float.abs c_t) (Float.abs c_f) (1e-3) (layout res) in *)
        res
      | FastDT.Node ({split;if_t;if_f}) ->
        Node (split, aux if_t, aux if_f)
    in
    aux dt

  let len dt =
    let rec aux = function
      | T -> 0
      | F -> 0
      | Leaf _ -> 1
      | Node (_, l, r) -> aux l + aux r + 1
    in
    aux dt

  let dt_summary dt fset =
    let len = (List.length fset) in
    let fv_arr = Array.init len (fun _ -> false) in
    let rec next idx =
      if idx >= len then None
      else if not (fv_arr.(idx)) then (Array.set fv_arr idx true; Some idx)
      else
        match next (idx + 1) with
        | None -> None
        | Some _ -> (Array.set fv_arr idx false; Some 0)
    in
    let posnum = ref 0 in
    let negnum = ref 0 in
    let rec aux idx =
      let fvec = Array.to_list fv_arr in
      let _ = Printf.printf "iter:%s\n" (boollist_to_string fvec) in
      let _ = if exec_vector dt fset fvec
        then posnum := !posnum + 1
        else negnum := !negnum + 1
      in
      match next idx with
      | None -> ()
      | Some idx -> aux idx
    in
    (aux 0; (!posnum, !negnum))

  let classify_ fset samples =
    let dt = FastDT.make_dt ~samples:samples ~max_d:50 in
    (* let _ = FastDT.print_tree' dt in *)
    (* let _ = if List.length labeled_vecs >= 3 then raise @@ InterExn "class" else () in *)
    let res = of_fastdt dt fset in
    (* let posnum, negnum = dt_summary res dfeature_set in *)
    (* let _ = Printf.printf "summary: %i|%i\n" posnum negnum in *)
    res

  let classify {FV.dfeature_set;FV.labeled_vecs} =
    let samples = List.map (fun (a, b) -> a, Array.of_list b) labeled_vecs in
    classify_ dfeature_set (Array.of_list samples)

  let classify_hash fset htab is_pos =
    (* let _ = Hashtbl.iter (fun vec label ->
     *     printf "%s:%s\n" (boollist_to_string vec) (layout_label label)
     *   ) htab in *)
    let samples = Array.init (Hashtbl.length htab)
        (fun _ -> false, Array.init (List.length fset) (fun _ -> false)) in
    let iter = ref 0 in
    let _ =
      Hashtbl.iter (fun f v ->
          let _ =
            if is_pos v
            then Array.set samples !iter (true, Array.of_list f)
            else Array.set samples !iter (false, Array.of_list f)
          in
          iter := !iter + 1
        ) htab
    in
    let dt = FastDT.make_dt ~samples:samples ~max_d:500 in
    let res = of_fastdt dt fset in
    let res_idx = of_fastdt_idx dt in
    res, res_idx

  let is_pos = function
    | Pos -> true
    | _ -> false

  let two_dt f fset dt1 dt2 =
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
    let ftab = Hashtbl.create 10000 in
    let rec aux idx =
      let fvec = Array.to_list fv_arr in
      (* let _ = Printf.printf "iter:%s\n" (boollist_to_string fvec) in *)
      let dt1_b = exec_vector_idx dt1 fvec in
      let dt2_b = exec_vector_idx dt2 fvec in
      let _ = if f dt1_b dt2_b then
          Hashtbl.add ftab fvec Pos
        else
          Hashtbl.add ftab fvec Neg
      in
      match next idx with
      | None -> ()
      | Some idx -> aux idx
    in
    (aux 0; classify_hash fset ftab is_pos)

  let merge_dt fset dt1 dt2 =
    two_dt (fun dt1_b dt2_b -> dt1_b || dt2_b) fset dt1 dt2

  let subtract_dt fset dt1 dt2 =
    two_dt (fun dt1_b dt2_b -> dt1_b && not dt2_b) fset dt1 dt2
end
