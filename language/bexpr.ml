module type Bexpr = sig
  module L: Lit.Lit
  type tp =
    | Bool
    | Int
    | IntList
    | IntTree
  type op = string

  type t =
    | Literal of tp * L.t
    | Var of tp * string
    | Op of tp * op * t list

  val eq_tp: tp * tp -> bool
  val layout_tp: tp -> string
  val layout: t -> string
end

module Bexpr (L: Lit.Lit) : Bexpr = struct
  module L = L
  type tp =
    | Bool
    | Int
    | IntList
    | IntTree
  type op = string

  type t =
    | Literal of tp * L.t
    | Var of tp * string
    | Op of tp * op * t list
  open Utils
  let layout_tp = function
    | Bool -> "bool"
    | Int -> "int"
    | IntList -> "int list"
    | IntTree -> "int tree"

  let eq_tp = function
    | (Int, Int) -> true
    | (Bool, Bool) -> true
    | (IntList, IntList) -> true
    | (IntTree, IntTree) -> true
    | _ -> false

let layout_op op args =
  match op, args with
  | "+", [a; b] -> Printf.sprintf "(%s+%s)" a b
  | "-", [a; b] -> Printf.sprintf "%s-%s" a b
  | "=", [a; b] -> Printf.sprintf "(%s==%s)" a b
  | "<>", [a; b] -> Printf.sprintf "(%s<>%s)" a b
  | ">=", [a; b] -> Printf.sprintf "(%s>=%s)" a b
  | "<=", [a; b] -> Printf.sprintf "(%s<=%s)" a b
  | ">", [a; b] -> Printf.sprintf "(%s>%s)" a b
  | "<", [a; b] -> Printf.sprintf "(%s<%s)" a b
  | pred, args -> Printf.sprintf "%s(%s)" pred (list_to_string (fun x -> x) args)

let rec layout = function
  | Literal (_, x) -> L.layout x
  | Var (_, name) -> name
  | Op (_, op, args) -> layout_op op (List.map layout args)


(* let rec layout_bexpr = function
 *   | Bop (op, args) -> layout_bop op (List.map layout_aexpr args)
 * 	| Member (dt, varname) -> Printf.sprintf "(member %s %s)" (layout_aexpr dt) varname
 * 	| Link (dt, uidx, vidx, u, v) ->
 *     Printf.sprintf "(link %s (%i:%s) (%i:%s))" (layout_aexpr dt) uidx u vidx v
 *   | Next (dt, uidx, vidx, u, v) ->
 *     Printf.sprintf "(next %s (%i:%s) (%i:%s))" (layout_aexpr dt) uidx u vidx v *)
end
