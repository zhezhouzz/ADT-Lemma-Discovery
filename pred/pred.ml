module type Pred = sig
  module E: Elem.Elem
  type t = string
  val layout : t -> string
  val apply_layout: (t * E.t * E.t list) -> string
  val apply: (t * E.t * E.t list) -> bool
  val desugar: t -> t * int list
  type pred_info = {name:string; num_dt:int; num_int: int; permu: bool}
  val raw_preds_info: pred_info list
  val preds_info: pred_info list
end

module Pred (E: Elem.Elem) : Pred with type E.t = E.t = struct
  module E = E
  open Utils
  open Printf
  type t = string
  type pred_info = {name:string; num_dt:int; num_int: int; permu: bool}
  let preds_info = [{name="member"; num_dt=1; num_int=1; permu=false};
                    {name="eq"; num_dt=0; num_int=2; permu=false};
                    {name="list_order"; num_dt=1; num_int=2; permu=true};]
  (* desugared *)
  let raw_preds_info = [{name="member"; num_dt=1; num_int=1; permu=false};
                        {name="order"; num_dt=1; num_int=4; permu=false};]
  let apply_layout (pred, dt, args) =
    sprintf "%s(%s, %s)" pred (E.layout dt) (List.to_string E.layout args)

  let layout name = name

  let member_apply (dt: E.t) (e: E.t) =
    match (dt, e) with
    | (E.L l, E.I e) -> List.exists (fun x -> x == e) l
    | (E.T t, E.I e) -> Tree.exists (fun x -> x == e) t
    | _ -> raise @@ InterExn "member_apply"

  let order_apply (dt: E.t) i0 i1 (e0: E.t) (e1: E.t) =
    let eq x y = x == y in
    match (dt, i0, i1, e0, e1) with
    | (E.L l, 0, 1, E.I e0, E.I e1) -> List.order eq l e0 e1
    | (E.T t, 0, 1, E.I e0, E.I e1) -> Tree.left_child eq t e0 e1
    | (E.T t, 0, 2, E.I e0, E.I e1) -> Tree.right_child eq t e0 e1
    | (E.T t, 1, 2, E.I e0, E.I e1) -> Tree.parallel_child eq t e0 e1
    | _ -> raise @@ InterExn "order_apply"

  let eq_apply (e0: E.t) (e1: E.t) =
    match e0, e1 with
    | (E.I e0, E.I e1) -> e0 == e1
    | _ -> raise @@ InterExn "eq_apply"

  let desugar pred =
    match pred with
    | "member" | "eq" | "order" -> pred, []
    | "list_order" -> "order", [0;1]
    | "tree_left" -> "order", [0;1]
    | "tree_right" -> "order", [0;2]
    | "tree_parallel" -> "order", [1;2]
    | _ -> raise @@ InterExn "desugar"

  let desugar_ (pred, dt, args) =
    let pred, args' = desugar pred in
    let args' = List.map (fun x -> E.I x) args' in
    (pred, dt, args' @ args)
    (* match pred with
     * | "member" | "eq" | "order" -> (pred, dt, args)
     * | "list_order" -> ("order", dt, (E.I 0) :: (E.I 1) :: args)
     * | "tree_left" -> ("order", dt, (E.I 0) :: (E.I 1) :: args)
     * | "tree_right" -> ("order", dt, (E.I 0) :: (E.I 2) :: args)
     * | "tree_parallel" -> ("order", dt, (E.I 1) :: (E.I 2) :: args)
     * | _ -> raise @@ InterExn "desugar_" *)

  let apply_ ((pred, dt, args) : t * E.t * E.t list) : bool =
    match pred, args with
    | "member", [arg] -> member_apply dt arg
    | "order", [E.I i0; E.I i1; arg0; arg1] -> order_apply dt i0 i1 arg0 arg1
    | "eq", [arg0; arg1] -> eq_apply arg0 arg1
    | _ -> raise @@ InterExn "apply"

  let apply ((pred, dt, args) : t * E.t * E.t list) : bool =
    let (pred, dt, args) = desugar_ (pred, dt, args) in
    apply_ (pred, dt, args)

end

module Predicate = Pred(Elem.Elem);;
module Element = Predicate.E;;
