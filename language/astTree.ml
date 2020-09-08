module type AstTree = sig
  module E: Epr.Epr
  type t =
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
    | SpecApply of string * string list
  type spec = (string list) * E.forallformula
  val layout: t -> string
  val layout_spec: spec -> string
end

module AstTree (E: Epr.Epr) : AstTree
  with type E.B.L.t = E.B.L.t
  with type E.B.tp = E.B.tp
  with type E.B.t = E.B.t
  with type E.t = E.t = struct
  module E = E
  open Utils
  open Printf
  type t =
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
    | SpecApply of string * string list
  type spec = (string list) * E.forallformula
  let rec layout = function
    (* | Atom bexpr -> sprintf "(%s)" (E.B.layout bexpr) *)
    | Implies (p1, p2) -> sprintf "(%s => %s)" (layout p1) (layout p2)
    | And ps -> inner_list_layout (List.map layout ps) "/\\" "true"
    | Or ps -> inner_list_layout (List.map layout ps) "\\/" "true"
    | Not p -> "~"^(layout p)
    | Iff (p1, p2) -> sprintf "(%s <=> %s)" (layout p1) (layout p2)
    | Ite (p1, p2, p3) ->
      sprintf "(ite %s %s %s)" (layout p1) (layout p2) (layout p3)
    | SpecApply (specname, args) ->
      sprintf "%s(%s)" specname (list_to_string (fun x ->x) args)
  let layout_spec (args, formula) =
    sprintf "fun %s -> %s" (list_to_string (fun x -> x) args) (E.layout_forallformula formula)
 end
