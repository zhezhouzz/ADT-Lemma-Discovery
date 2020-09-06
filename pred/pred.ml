module type Pred = sig
  module E: Elem.Elem
  type t = string
  val layout : t -> string
  val apply_layout: (t * E.t * E.t list) -> string
  val apply: (t * E.t * E.t list) -> bool
end

module Pred (E: Elem.Elem) : Pred = struct
  module E = E
  open Utils
  open Printf
  type t = string
  let apply_layout (pred, dt, args) =
    sprintf "%s(%s, %s)" pred (E.layout dt) (list_to_string E.layout args)

  let layout name = name

  let member_apply (dt: E.t) (e: E.t) =
    match (dt, e) with
    | (E.L l, E.I e) -> List.exists (fun x -> x == e) l
    | (E.T t, E.I e) -> Tree.exists (fun x -> x == e) t
    | _ -> raise @@ InterExn "member_apply"

  let order_apply (dt: E.t) i0 i1 (e0: E.t) (e1: E.t) =
    let eq x y = x == y in
    match (dt, i0, i1, e0, e1) with
    | (E.L l, 0, 1, E.I e0, E.I e1) -> list_order eq l e0 e1
    | (E.T t, 0, 1, E.I e0, E.I e1) -> Tree.left_child eq t e0 e1
    | (E.T t, 0, 2, E.I e0, E.I e1) -> Tree.right_child eq t e0 e1
    | (E.T t, 1, 2, E.I e0, E.I e1) -> Tree.parallel_child eq t e0 e1
    | _ -> raise @@ InterExn "order_apply"

  let eq_apply (e0: E.t) (e1: E.t) =
    match e0, e1 with
    | (E.I e0, E.I e1) -> e0 == e1
    | _ -> raise @@ InterExn "eq_apply"

  let desugar (pred, dt, args) =
    match pred with
    | "member" | "eq" | "order" -> (pred, dt, args)
    | "list_order" -> ("order", dt, (E.I 0) :: (E.I 1) :: args)
    | "tree_left" -> ("order", dt, (E.I 0) :: (E.I 1) :: args)
    | "tree_right" -> ("order", dt, (E.I 0) :: (E.I 2) :: args)
    | "tree_parallel" -> ("order", dt, (E.I 1) :: (E.I 2) :: args)
    | _ -> raise @@ InterExn "desugar"

  let apply_ ((pred, dt, args) : t * E.t * E.t list) : bool =
    match pred, args with
    | "member", [arg] -> member_apply dt arg
    | "order", [E.I i0; E.I i1; arg0; arg1] -> order_apply dt i0 i1 arg0 arg1
    | "eq", [arg0; arg1] -> eq_apply arg0 arg1
    | _ -> raise @@ InterExn "apply"

  let apply ((pred, dt, args) : t * E.t * E.t list) : bool =
    let (pred, dt, args) = desugar (pred, dt, args) in
    apply_ (pred, dt, args)
end
