module type Dtree = sig
  type value = Preds.Pred.Value.t
  type feature = Preds.Pred.Predicate.t * int list
  type t =
    | T
    | F
    | Leaf of feature
    | Node of feature * t * t
  val exec: t -> value list -> bool
  val exec_feature: feature -> value -> value list -> bool
  val exec_raw: t -> feature list ->  bool list -> bool
  val layout_feature: feature -> string
  val layout: t -> string
  val to_forallformula: t -> dtname:string -> Language.SpecAst.E.forallformula
  val feature_to_epr: feature -> dtname:string ->
    fv:Language.SpecAst.E.SE.t list -> Language.SpecAst.E.t
end

module Dtree : Dtree = struct
  module Epr = Language.SpecAst.E
  module P = Preds.Pred.Predicate
  open Utils
  open Printf
  type value = P.V.t
  type feature = P.t * int list
  type t =
    | T
    | F
    | Leaf of feature
    | Node of feature * t * t

  let exec_feature (pred, ids) (dt: value) (args: value list) =
    let lookup i =
      match List.nth_opt args i with
      | None -> raise @@ InterExn "exec_feature::lookup"
      | Some v -> v
    in
    P.apply (pred, dt, (List.map lookup ids))

  let leaf_apply (pred, ids) (args: value list) =
    match args with
    | [] -> raise @@ InterExn "dtree leaf_apply"
    | dt :: args -> (exec_feature (pred, ids) dt args)

  let exec (dt: t) (args: value list) : bool =
    let rec aux = function
      | T -> true
      | F -> false
      | Leaf (pred, ids) -> (leaf_apply (pred, ids) args)
      | Node (feature, l, r) ->
        if leaf_apply feature args
        then aux l
        else aux r
    in
    aux dt

  let feature_eq (pred, ids) (pred', ids') =
    (String.equal pred pred') && (IntList.eq ids ids')

  let exec_raw (dt: t) (fl: feature list) (vec: bool list) : bool =
    let m = List.combine fl vec in
    let get_b f =
      match List.find_opt (fun (f', _) -> feature_eq f f') m with
      | None -> raise @@ InterExn "exec_raw"
      | Some (_, b) -> b
    in
    let rec aux = function
      | T -> true
      | F -> false
      | Leaf feature -> get_b feature
      | Node (feature, l, r) ->
        if get_b feature
        then aux l
        else aux r
    in
    aux dt

  let vartable = List.fold_left (fun m (k,v) ->
      IntMap.add k v m
    ) IntMap.empty [0, "u";1, "v";2, "w"]

  let layout_feature (pred, ids) =
    let args = List.map (fun id -> IntMap.find id vartable) ids in
    sprintf "%s(%s)" (P.layout pred) (List.to_string (fun x -> x) args)

  let rec layout = function
    | T -> "⊥"
    | F -> "⊥"
    | Leaf feature -> layout_feature feature
    | Node (feature, l, r) ->
      sprintf "[%s](%s,%s)" (layout_feature feature) (layout l) (layout r)

  let to_epr_ pred dtname args =
    let info = List.find (fun info -> String.equal info.P.name pred) P.preds_info in
    if info.num_dt == 0 then
      Epr.Atom (Epr.SE.Op (Epr.SE.Bool, pred, args))
    else
      Epr.Atom (Epr.SE.Op (Epr.SE.Bool, pred, (Epr.SE.Var (Epr.SE.IntList, dtname)) ::args))

  let used_ids (dtree: t) =
    let rec aux = function
      | T | F -> []
      | Leaf (_, ids) -> ids
      | Node ((_, ids), l, r) ->
        List.remove_duplicates (fun x y -> x == y) (ids @ (aux l) @ (aux r))
    in
    aux dtree

  let to_forallformula (dtree: t) ~dtname : Epr.forallformula =
    let ids = used_ids dtree in
    let feature_to_bexpr (pred, ids) =
      let args = List.map (fun id -> Epr.SE.Var (Epr.SE.Int, IntMap.find id vartable)) ids in
      to_epr_ pred dtname args
    in
    let rec aux = function
      | T -> Epr.True
      | F -> Epr.Not Epr.True
      | Leaf feature -> feature_to_bexpr feature
      | Node (feature, l, r) -> Epr.Ite (feature_to_bexpr feature, aux l, aux r)
    in
    dtname::(List.map (fun id -> IntMap.find id vartable) ids), aux dtree
  let feature_to_epr (pred, argsid) ~dtname ~fv =
    let args = List.map (fun id -> List.nth fv id) argsid in
    to_epr_ pred dtname args
end
