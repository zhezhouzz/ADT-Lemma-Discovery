module Tp = struct
  type t =
    | Bool
    | Int
    | IntList
    | IntTree

  let layout = function
    | Bool -> "bool"
    | Int -> "int"
    | IntList -> "int list"
    | IntTree -> "int tree"

  let is_dt = function
    | Int -> false
    | Bool -> false
    | IntList -> true
    | IntTree -> true

  let eq_tp_ = function
    | (Int, Int) -> true
    | (Bool, Bool) -> true
    | (IntList, IntList) -> true
    | (IntTree, IntTree) -> true
    | _ -> false
  let eq a b = eq_tp_ (a, b)
end
