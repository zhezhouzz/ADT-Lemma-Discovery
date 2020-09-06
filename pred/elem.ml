module type Elem = sig
  type t =
    | L of int list
    | T of int Utils.Tree.t
    | I of int
    | B of bool
    | NotADt
  val layout : t -> string
end

module Elem: Elem = struct
  open Utils
  open Printf
  type t =
    | L of int list
    | T of int Utils.Tree.t
    | I of int
    | B of bool
    | NotADt
  let layout = function
    | L l -> sprintf "[%s]" (intlist_to_string l)
    | T tr -> Tree.layout string_of_int tr
    | I i -> string_of_int i
    | B b -> string_of_bool b
    | NotADt -> "_"
end
