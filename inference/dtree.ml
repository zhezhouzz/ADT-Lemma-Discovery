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
end

module Dtree : Dtree = struct
  module Epr = Language.SpecAst.E
  module P = Pred.Pred
  module T = Tp.Tp
  module F = Feature.Feature
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
    | T -> "⊥"
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
        if (Float.abs c_t) < 1e-3 then F
        else if (Float.abs c_f) < 1e-3 then T
        else raise @@ InterExn (sprintf "Bad Dt Result(%f, %f)" c_t c_f)
      | FastDT.Node ({split;if_t;if_f}) ->
        match List.nth_opt feature_set split with
        | None -> raise @@ InterExn "Bad Dt Result"
        | Some p -> Node (p, aux if_t, aux if_f)
    in
    aux dt
end
