open Utils
open Atom

type tp = Int | Bool | Dt

type t =
  | True
  | Atom of bexpr
  | Implies of t * t
  | Ite of t * t * t
  | Not of t
  | And of t list
  | Or of t list
  | Iff of t * t
  | BApp of string * aexpr list
	| Forall of (string list) * t

type spec = string * string list * string list * t

let tp_eq = function
  | (Int, Int) -> true
  | (Bool, Bool) -> true
  | (Dt, Dt) -> true
  | _ -> false

let tp_layout = function
  | Int -> "Int"
  | Bool -> "Bool"
  | Dt -> "Dt"

let rec layout = function
  | True -> "true"
  | Atom bexpr -> Printf.sprintf "(%s)" (layout_bexpr bexpr)
  | Implies (p1, p2) -> Printf.sprintf "(%s => %s)" (layout p1) (layout p2)
  | And ps -> inner_list_layout (List.map layout ps) "/\\" "true"
  | Or ps -> inner_list_layout (List.map layout ps) "\\/" "true"
  | Not p -> "~"^(layout p)
  | Iff (p1, p2) -> Printf.sprintf "(%s <=> %s)" (layout p1) (layout p2)
  | Ite (p1, p2, p3) ->
    Printf.sprintf "(ite %s %s %s)" (layout p1) (layout p2) (layout p3)
  | BApp (fname, args) ->
    Printf.sprintf "(%s %s)" fname
      (inner_list_layout (List.map layout_aexpr args) " " "")
	| Forall (_, _) -> raise @@ ZZExn "layout: undefined"

let layout_spec (_, _, forallvars, body) =
  Printf.sprintf "forall%s,%s" (inner_list_layout forallvars " " "") (layout body)

let t_eq a b = Atom (Bop ("=", [a; b]))
let t_neq a b = Atom (Bop ("<>", [a; b]))
let t_and a b = And [a;b]
let list_order lname u v = Link (AVar lname, 0, 1, u, v)
let list_next lname u v = Next (AVar lname, 0, 1, u, v)
