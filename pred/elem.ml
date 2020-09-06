module type Elem = sig
  type t =
    | L of int list
    | T of int Utils.Tree.t
    | I of int
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
    | NotADt
  let layout = function
    | L l -> sprintf "[%s]" (intlist_to_string l)
    | T tr -> Tree.layout string_of_int tr
    | I i -> string_of_int i
    | NotADt -> "_"
end
