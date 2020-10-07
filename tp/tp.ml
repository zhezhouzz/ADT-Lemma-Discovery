module Tp = struct
  type t =
    | Bool
    | Int
    | IntList
    | IntTree
    | IntTreeI
    | IntTreeB


  let layout = function
    | Bool -> "bool"
    | Int -> "int"
    | IntList -> "int list"
    | IntTree -> "int tree"
    | IntTreeI -> "int treei"
    | IntTreeB -> "int treeb"

  let is_dt = function
    | Int -> false
    | Bool -> false
    | IntList -> true
    | IntTree -> true
    | IntTreeI -> true
    | IntTreeB -> true

  let eq_tp_ = function
    | (Int, Int) -> true
    | (Bool, Bool) -> true
    | (IntList, IntList) -> true
    | (IntTree, IntTree) -> true
    | (IntTreeI, IntTreeI) -> true
    | (IntTreeB, IntTreeB) -> true
    | _ -> false
  let eq a b = eq_tp_ (a, b)
  open Utils
  let make_name tp =
    let name =
      match tp with
      | Int -> Renaming.unique "x"
      | IntList -> Renaming.unique "l"
      | IntTree | IntTreeI | IntTreeB -> Renaming.unique "tr"
      | Bool -> Renaming.unique "b"
    in
    tp, name
end
