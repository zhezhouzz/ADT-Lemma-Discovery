module type Dtree = sig
  type value = Pred.Value.t
  type feature = Feature.Feature.t
  type feature_set = Feature.Feature.set
  type t =
    | T
    | F
    | Leaf of feature
    | Node of feature * t * t
  val exec: t -> value Utils.StrMap.t -> bool
  val exec_vector: t -> feature_set -> bool list -> bool
  val layout: t -> string
  val to_epr: t -> Language.SpecAst.E.t
  val to_forallformula: t -> Language.SpecAst.E.forallformula
  val to_spec: t -> Language.SpecAst.spec
  val of_fastdt: Ml.FastDT.FastDT.dt -> feature_set -> t
  val classify: Sample.FeatureVector.data -> t
  val len: t -> int
  val dt_summary: t -> feature_set -> (int * int)
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
  type t =
    | T
    | F
    | Leaf of feature
    | Node of feature * t * t

  let exec (dt: t) m : bool =
    let rec aux = function
      | T -> true
      | F -> false
      | Leaf feature -> F.exec feature m
      | Node (feature, l, r) ->
        if F.exec feature m then aux l else aux r
    in
    aux dt

  let exec_vector (dt: t) (fl: feature list) (vec: bool list) : bool =
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

  let rec layout = function
    | T -> "⊤"
    | F -> "⊥"
    | Leaf feature -> F.layout feature
    | Node (feature, l, r) ->
      sprintf "[%s](%s,%s)" (F.layout feature) (layout l) (layout r)

  let get_vars (dtree: t) =
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

  let to_forallformula (dtree: t) =
    let dts, elems = get_vars dtree in
    dts @ elems, to_epr dtree

  let to_spec (dtree: t) =
    let dts, elems = get_vars dtree in
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

  let classify {FV.dfeature_set;FV.labeled_vecs} =
    let samples = List.map (fun (a, b) -> a, Array.of_list b) labeled_vecs in
    let dt = FastDT.make_dt ~samples:(Array.of_list samples) ~max_d:50 in
    let _ = FastDT.print_tree' dt in
    (* let _ = if List.length labeled_vecs >= 3 then raise @@ InterExn "class" else () in *)
    let res = of_fastdt dt dfeature_set in
    (* let posnum, negnum = dt_summary res dfeature_set in *)
    (* let _ = Printf.printf "summary: %i|%i\n" posnum negnum in *)
    res

end
