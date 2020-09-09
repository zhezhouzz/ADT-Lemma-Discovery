module type EprTree = sig
  module B: Bexpr.Bexpr
  type t =
    | True
    | Atom of B.t
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
  type free_variable = string
  type forallformula = free_variable list * t
  val layout: t -> string
  val layout_forallformula: forallformula -> string
end

module EprTree(B: Bexpr.Bexpr) : EprTree
  with type B.L.t = B.L.t
  with type B.tp = B.tp
  with type B.t = B.t = struct
  module B = B
  open Utils

  type t =
    | True
    | Atom of B.t
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
  type free_variable = string
  type forallformula = free_variable list * t

  let rec layout = function
    | True -> "true"
    | Atom bexpr -> Printf.sprintf "(%s)" (B.layout bexpr)
    | Implies (p1, p2) -> Printf.sprintf "(%s => %s)" (layout p1) (layout p2)
    | And ps -> inner_list_layout (List.map layout ps) "/\\" "true"
    | Or ps -> inner_list_layout (List.map layout ps) "\\/" "true"
    | Not p -> "~"^(layout p)
    | Iff (p1, p2) -> Printf.sprintf "(%s <=> %s)" (layout p1) (layout p2)
    | Ite (p1, p2, p3) ->
      Printf.sprintf "(ite %s %s %s)" (layout p1) (layout p2) (layout p3)

  let layout_forallformula (forallvars, body) =
    if (List.length forallvars) == 0 then layout body else
    Printf.sprintf "forall %s,%s" (inner_list_layout forallvars " " "") (layout body)

  (* let t_eq a b = Atom (Bop ("=", [a; b]))
   * let t_neq a b = Atom (Bop ("<>", [a; b]))
   * let t_and a b = And [a;b]
   * let list_order lname u v = Link (AVar lname, 0, 1, u, v)
   * let list_next lname u v = Next (AVar lname, 0, 1, u, v) *)
end
