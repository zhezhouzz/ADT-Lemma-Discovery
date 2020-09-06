module type Ast = sig
  module E: Epr.Epr
  type t =
    | Atom of E.B.t
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
    | SpecApply of string * E.B.t list
  type spec_table = E.spec Utils.IntMap.t
  val layout: t -> string
end

module Ast (E: Epr.Epr) : Ast = struct
  module E = E
  open Utils
  type t =
    | Atom of E.B.t
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
    | SpecApply of string * E.B.t list
  type spec_table = E.spec Utils.IntMap.t
  let rec layout = function
    | Atom bexpr -> Printf.sprintf "(%s)" (E.B.layout bexpr)
    | Implies (p1, p2) -> Printf.sprintf "(%s => %s)" (layout p1) (layout p2)
    | And ps -> inner_list_layout (List.map layout ps) "/\\" "true"
    | Or ps -> inner_list_layout (List.map layout ps) "\\/" "true"
    | Not p -> "~"^(layout p)
    | Iff (p1, p2) -> Printf.sprintf "(%s <=> %s)" (layout p1) (layout p2)
    | Ite (p1, p2, p3) ->
      Printf.sprintf "(ite %s %s %s)" (layout p1) (layout p2) (layout p3)
    | SpecApply (specname, args) ->
      Printf.sprintf "%s(%s)" specname (list_to_string E.B.layout args)
 end
