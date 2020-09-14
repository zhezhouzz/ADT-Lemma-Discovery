module type AstTree = sig
  module E: Epr.Epr
  type t =
    | ForAll of E.forallformula
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
    | SpecApply of string * E.SE.t list
  type spec = (string list) * E.forallformula
  val layout: t -> string
  val layout_spec: spec -> string
end

module AstTree (E: Epr.Epr) : AstTree
  with type E.SE.L.t = E.SE.L.t
  with type E.SE.tp = E.SE.tp
  with type E.SE.t = E.SE.t
  with type E.t = E.t = struct
  module E = E
  open Utils
  open Printf
  type t =
    | ForAll of E.forallformula
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
    | SpecApply of string * E.SE.t list
  type spec = (string list) * E.forallformula
  let rec layout = function
    | ForAll ff -> E.layout_forallformula ff
    | Implies (p1, p2) -> sprintf "(%s => %s)" (layout p1) (layout p2)
    | And ps -> List.inner_layout (List.map layout ps) "/\\" "true"
    | Or ps -> List.inner_layout (List.map layout ps) "\\/" "true"
    | Not p -> "~"^(layout p)
    | Iff (p1, p2) -> sprintf "(%s <=> %s)" (layout p1) (layout p2)
    | Ite (p1, p2, p3) ->
      sprintf "(ite %s %s %s)" (layout p1) (layout p2) (layout p3)
    | SpecApply (specname, args) ->
      sprintf "%s(%s)" specname (List.to_string E.SE.layout args)
  let layout_spec (args, formula) =
    sprintf "fun %s -> %s" (List.to_string (fun x -> x) args) (E.layout_forallformula formula)
 end
