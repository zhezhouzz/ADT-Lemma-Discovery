(* module type Elem = sig
 *   type t =
 *     | L of int list
 *     | T of int Utils.Tree.t
 *     | I of int
 *     | NotADt
 *   val layout : t -> string
 * end
 * 
 * module Elem: Elem = struct
 *   open Utils
 *   open Printf
 *   type t =
 *     | L of int list
 *     | T of int Utils.Tree.t
 *     | I of int
 *     | NotADt
 *   let layout = function
 *     | L l -> sprintf "[%s]" (intlist_to_string l)
 *     | T tr -> Tree.layout string_of_int tr
 *     | I i -> string_of_int i
 *     | NotADt -> "_"
 * end *)
(* module type Pred = sig
 *   module E: Elem
 *   type t = string
 *   val layout : t -> string
 *   val apply_layout: (t * E.t * E.t list) -> string
 *   val apply: (t * E.t * E.t list) -> bool
 * end
 * 
 * module Pred (E: Elem) : Pred = struct
 *   module E = E
 *   open Utils
 *   open Printf
 *   type t = string
 *   let apply_layout (pred, dt, args) =
 *     sprintf "%s(%s, %s)" pred (E.layout dt) (list_to_string E.layout args)
 * 
 *   let layout name = name
 * 
 *   let member_apply (dt: E.t) (e: E.t) =
 *     match (dt, e) with
 *     | (E.L l, E.I e) -> List.exists (fun x -> x == e) l
 *     | (E.T t, E.I e) -> Tree.exists (fun x -> x == e) t
 *     | _ -> raise @@ InterExn "member_apply"
 * 
 *   let order_apply (dt: E.t) i0 i1 (e0: E.t) (e1: E.t) =
 *     let eq x y = x == y in
 *     match (dt, i0, i1, e0, e1) with
 *     | (E.L l, 0, 1, E.I e0, E.I e1) -> list_order eq l e0 e1
 *     | (E.T t, 0, 1, E.I e0, E.I e1) -> Tree.left_child eq t e0 e1
 *     | (E.T t, 0, 2, E.I e0, E.I e1) -> Tree.right_child eq t e0 e1
 *     | (E.T t, 1, 2, E.I e0, E.I e1) -> Tree.parallel_child eq t e0 e1
 *     | _ -> raise @@ InterExn "order_apply"
 * 
 *   let eq_apply (e0: E.t) (e1: E.t) =
 *     match e0, e1 with
 *     | (E.I e0, E.I e1) -> e0 == e1
 *     | _ -> raise @@ InterExn "eq_apply"
 * 
 *   let desugar (pred, dt, args) =
 *     match pred with
 *     | "member" | "eq" | "order" -> (pred, dt, args)
 *     | "list_order" -> ("order", dt, (E.I 0) :: (E.I 1) :: args)
 *     | "tree_left" -> ("order", dt, (E.I 0) :: (E.I 1) :: args)
 *     | "tree_right" -> ("order", dt, (E.I 0) :: (E.I 2) :: args)
 *     | "tree_parallel" -> ("order", dt, (E.I 1) :: (E.I 2) :: args)
 *     | _ -> raise @@ InterExn "desugar"
 * 
 *   let apply_ ((pred, dt, args) : t * E.t * E.t list) : bool =
 *     match pred, args with
 *     | "member", [arg] -> member_apply dt arg
 *     | "order", [E.I i0; E.I i1; arg0; arg1] -> order_apply dt i0 i1 arg0 arg1
 *     | "eq", [arg0; arg1] -> eq_apply arg0 arg1
 *     | _ -> raise @@ InterExn "apply"
 * 
 *   let apply ((pred, dt, args) : t * E.t * E.t list) : bool =
 *     let (pred, dt, args) = desugar (pred, dt, args) in
 *     apply_ (pred, dt, args)
 * end *)
module AxiomSyn (P: Pred.Pred) = struct
  open Utils
  open Printf
module E = P.E
type vec = bool list
type sample = {dt: E.t; args: E.t list; vec: vec}
type feature = P.t * int list
type title = feature list
type result =
  | T
  | F
  | Atom of feature
  | Ite of feature * result * result

let vartable = List.fold_left (fun m (k,v) ->
    IntMap.add k v m
  ) IntMap.empty [0, "u";1, "v";2, "w"]

let layout_title (title: title) =
  let playout (pred, ids) =
    let args = List.map (fun id -> IntMap.find id vartable) ids in
    sprintf "%s(%s)" (P.layout pred) (list_to_string (fun x -> x) args)
  in
  List.fold_left (fun r pred -> sprintf "%s [%s]" r (playout pred)) "" title

let feature_apply (pred, ids) (dt: E.t) (args: E.t list) =
  let lookup i =
    match List.nth_opt args i with
    | None -> raise @@ InterExn "feature_apply::lookup"
    | Some v -> v
  in
  P.apply (pred, dt, (List.map lookup ids))

let make_sample (title:title) (dt: E.t) (args: E.t list) =
  let vec = List.map (fun feature -> feature_apply feature dt args) title in
  {dt; args; vec}

let cex_to_sample (args: E.t list) (vec: bool list) =
  {dt = E.NotADt; args; vec}

let layout_sample {dt; args; vec} =
  sprintf "%s(%s) [%s]" (E.layout dt) (list_to_string E.layout args) (boollist_to_string vec)

let classify (title: title) (_:vec) : result =
  let member0 = List.nth title 0 in
  let ord = List.nth title 2 in
  Ite (ord, Atom member0, T)

let result_apply (result:result) (dt: E.t) (args: E.t list) =
  let rec aux = function
    | T -> true
    | F -> false
    | Atom feature -> feature_apply feature dt args
    | Ite (feature, l, r) ->
      if feature_apply feature dt args
      then aux l
      else aux r
  in
  aux result
end
