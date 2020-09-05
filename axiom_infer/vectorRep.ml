module type Elem = sig
  type t =
    | L of int list
    | T of int Utils.Tree.t
    | I of int
  val layout : t -> string
end

module Elem: Elem = struct
  open Utils
  open Printf
  type t =
    | L of int list
    | T of int Utils.Tree.t
    | I of int
  let layout = function
    | L l -> sprintf "[%s]" (intlist_to_string l)
    | T tr -> Tree.layout string_of_int tr
    | I i -> string_of_int i
end

module type Pred = sig
  module E: Elem
  type t
  val layout : t -> string
  val apply: t -> E.t -> E.t list -> bool
end

module P (E: Elem) : Pred = struct
  module E = E
  open Utils
  (* open Printf *)
  type t = string
  (* let vartable = List.fold_left (fun m (k,v) ->
   *     IntMap.add k v m
   *   ) IntMap.empty [0, "u";1, "v";2, "w"] *)
  (* let layout (name, args) =
   *   sprintf "%s(dt, %s)" name
   *     (list_to_string (fun x -> x) (List.map (fun i -> IntMap.find i vartable) args)) *)

  let layout name = name

  let member_apply (dt: E.t) (e: E.t) =
    match (dt, e) with
    | (E.L l, E.I e) -> List.exists (fun x -> x = e) l
    | (E.T t, E.I e) -> Tree.exists (fun x -> x = e) t
    | _ -> raise @@ InterExn "member_apply"

  let order_apply (dt: E.t) i0 i1 (e0: E.t) (e1: E.t) =
    let eq x y = x = y in
    match (dt, i0, i1, e0, e1) with
    | (E.L l, 0, 1, E.I e0, E.I e1) -> list_order eq l e0 e1
    | (E.T t, 0, 1, E.I e0, E.I e1) -> Tree.left_child eq t e0 e1
    | (E.T t, 0, 2, E.I e0, E.I e1) -> Tree.right_child eq t e0 e1
    | (E.T t, 1, 2, E.I e0, E.I e1) -> Tree.parallel_child eq t e0 e1
    | _ -> raise @@ InterExn "order_apply"

  let eq_apply (e0: E.t) (e1: E.t) =
    match e0, e1 with
    | (E.I e0, E.I e1) -> e0 = e1
    | _ -> raise @@ InterExn "eq_apply"

  let apply name (dt: E.t) (args: E.t list) =
    match name, args with
    | "member", [arg] -> member_apply dt arg
    | "order", [E.I i0; E.I i1; arg0; arg1] -> order_apply dt i0 i1 arg0 arg1
    | "eq", [arg0; arg1] -> eq_apply arg0 arg1
    | _ -> raise @@ InterExn "apply"
end

module VecRep (E: Elem) (P: Pred)= struct
  open Utils
  open Printf
type t = {dt: E.t; args: E.t list; vec: bool list}
type title = P.t list

let layout_title (title: title) =
  List.fold_left (fun r pred -> sprintf "%s [%s]" r (P.layout pred)) "" title

let layout_vector ({dt;args;vec}:t) =
  sprintf "%s(%s) [%s]" (E.layout dt) (list_to_string E.layout args) (boollist_to_string vec)

end
