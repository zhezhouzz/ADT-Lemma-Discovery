module type Lit = sig
  type t =
    | Int of int
    | Bool of bool
    | IntList of int list
    | IntTree of int Utils.Tree.t
  val layout : t -> string
end

module Lit : Lit = struct
  type t =
    | Int of int
    | Bool of bool
    | IntList of int list
    | IntTree of int Utils.Tree.t
  let layout = function
    | Int x -> string_of_int x
    | Bool b -> string_of_bool b
    | IntList l -> Utils.intlist_to_string l
    | IntTree t -> Utils.Tree.layout string_of_int t
end
