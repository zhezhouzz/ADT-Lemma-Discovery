module type EprTree = sig
  module SE: SimpleExpr.SimpleExpr
  type t =
    | True
    | Atom of SE.t
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
  val subst: t -> string list -> SE.t list -> t
  val subst_forallformula: forallformula -> string list -> SE.t list -> forallformula
  val eq: t -> t -> bool
  val eq_forallformula: forallformula -> forallformula -> bool
end

module EprTree(SE: SimpleExpr.SimpleExpr) : EprTree
  with type SE.L.t = SE.L.t
  with type SE.tp = SE.tp
  with type SE.t = SE.t = struct
  module SE = SE
  open Utils

  type t =
    | True
    | Atom of SE.t
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
    | Atom bexpr -> Printf.sprintf "(%s)" (SE.layout bexpr)
    | Implies (p1, p2) -> Printf.sprintf "(%s => %s)" (layout p1) (layout p2)
    | And ps -> List.inner_layout (List.map layout ps) "/\\" "true"
    | Or ps -> List.inner_layout (List.map layout ps) "\\/" "true"
    | Not p -> "~"^(layout p)
    | Iff (p1, p2) -> Printf.sprintf "(%s <=> %s)" (layout p1) (layout p2)
    | Ite (p1, p2, p3) ->
      Printf.sprintf "(ite %s %s %s)" (layout p1) (layout p2) (layout p3)

  let layout_forallformula (forallvars, body) =
    if (List.length forallvars) == 0 then layout body else
      Printf.sprintf "forall %s,%s" (List.inner_layout forallvars " " "") (layout body)

  let subst body args argsvalue =
    let rec aux = function
      | True -> True
      | Atom bexpr -> Atom (SE.subst bexpr args argsvalue)
      | Implies (p1, p2) -> Implies (aux p1, aux p2)
      | And ps -> And (List.map aux ps)
      | Or ps -> Or (List.map aux ps)
      | Not p -> Not (aux p)
      | Iff (p1, p2) -> Iff (aux p1, aux p2)
      | Ite (p1, p2, p3) -> Ite (aux p1, aux p2, aux p3)
    in
    aux body

  let subst_forallformula (fv, body) args argsvalue =
    fv, subst body args argsvalue

  let eq a b =
    let rec aux a b =
      match (a, b) with
      | True, True -> true
      | Atom expr1, Atom expr2 -> SE.eq expr1 expr2
      | Implies (p1, p2), Implies (p1', p2') -> (aux p1 p1') && (aux p2 p2')
      | And ps1, And ps2 -> List.for_all2 aux ps1 ps2
      | Or ps1, Or ps2 -> List.for_all2 aux ps1 ps2
      | Not p1, Not p2 -> aux p1 p2
      | Iff (p1, p2), Iff (p1', p2') -> (aux p1 p1') && (aux p2 p2')
      | Ite (p1, p2, p3), Ite (p1', p2', p3') -> (aux p1 p1') && (aux p2 p2') && (aux p3 p3')
      | _ -> false
    in
    aux a b

  let eq_forallformula (fv1, body1) (fv2, body2) =
    (List.for_all2 String.equal fv1 fv2) && (eq body1 body2)
end
