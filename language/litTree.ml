module type LitTree = sig
  type t =
    | Int of int
    | Bool of bool
    | IntList of int list
    | IntTree of int Utils.Tree.t
  val layout : t -> string
  val eq : t -> t -> bool
end

module LitTree : LitTree = struct
  type t =
    | Int of int
    | Bool of bool
    | IntList of int list
    | IntTree of int Utils.Tree.t
  open Utils
  let layout = function
    | Int x -> string_of_int x
    | Bool b -> string_of_bool b
    | IntList l -> IntList.to_string l
    | IntTree t -> Tree.layout string_of_int t
  let eq x y =
    let aux = function
      | (Int x, Int y) -> x == y
      | (Bool x, Bool y) -> x == y
      | (IntList x, IntList y) -> List.eq (fun x y -> x == y) x y
      | (IntTree x, IntTree y) -> Tree.eq (fun x y -> x == y) x y
      | (_, _) -> false
    in
    aux (x, y)
end
