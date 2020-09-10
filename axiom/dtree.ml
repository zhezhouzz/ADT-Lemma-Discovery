module type Dtree = sig
  type et = Preds.Pred.Element.t
  type feature = Preds.Pred.Predicate.t * int list
  type t =
    | T
    | F
    | Leaf of feature
    | Node of feature * t * t
  val exec: t -> et list -> bool
  val exec_feature: feature -> et -> et list -> bool
  val layout_feature: feature -> string
  val layout: t -> string
  val to_epr: t -> Language.Ast.SpecAst.E.t
end

module Dtree : Dtree = struct
  module Epr = Language.Ast.SpecAst.E
  module P = Preds.Pred.Predicate
  open Utils
  open Printf
  type et = P.E.t
  type feature = P.t * int list
  type t =
    | T
    | F
    | Leaf of feature
    | Node of feature * t * t

  let exec_feature (pred, ids) (dt: et) (args: et list) =
    let lookup i =
      match List.nth_opt args i with
      | None -> raise @@ InterExn "exec_feature::lookup"
      | Some v -> v
    in
    P.apply (pred, dt, (List.map lookup ids))

  let leaf_apply (pred, ids) (args: et list) =
    match args with
    | [] -> raise @@ InterExn "dtree leaf_apply"
    | dt :: args -> (exec_feature (pred, ids) dt args)

  let exec (dt: t) (args: et list) : bool =
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

  let to_epr (dtree: t) : Epr.t =
    let feature_to_bexpr (pred, ids) =
      let args = List.map (fun id -> Epr.B.Var (Epr.B.Int, IntMap.find id vartable)) ids in
      Epr.Atom (Epr.B.Op (Epr.B.Bool, pred, (Epr.B.Var (Epr.B.IntList, "l"))::args))
    in
    let rec aux = function
      | T -> Epr.True
      | F -> Epr.Not Epr.True
      | Leaf feature -> feature_to_bexpr feature
      | Node (feature, l, r) -> Epr.Ite (feature_to_bexpr feature, aux l, aux r)
    in
    aux dtree
end
