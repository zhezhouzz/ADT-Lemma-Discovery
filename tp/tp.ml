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

  type tp_counter = {
    boolnum: int;
    intnum: int;
    ilistnum: int;
    itreenum: int;
    itreeinum: int;
    itreebnum: int;
  }
  let make_counter () =
    {boolnum = 0; intnum = 0; ilistnum = 0;
     itreenum = 0; itreeinum = 0; itreebnum = 0;}
  let counter_set counter tp =
    let name s i = Printf.sprintf "%s_%i" s i in
    match tp with
    | Bool -> name "b" counter.boolnum, {counter with boolnum = counter.boolnum + 1}
    | Int -> name "i" counter.intnum, {counter with intnum = counter.intnum + 1}
    | IntList -> name "il" counter.ilistnum, {counter with ilistnum = counter.ilistnum + 1}
    | IntTree -> name "it" counter.itreenum, {counter with itreenum = counter.itreenum + 1}
    | IntTreeI -> name "iti"
                    counter.itreeinum, {counter with itreeinum = counter.itreeinum + 1}
    | IntTreeB -> name "itb" counter.itreebnum, {counter with itreebnum = counter.itreebnum + 1}

  let auto_name tps =
    let res, _ =
    List.fold_left (fun (r, counter) tp ->
        let name, counter = counter_set counter tp in
        r @ [name], counter
        ) ([], make_counter ()) tps
    in
    res
end
