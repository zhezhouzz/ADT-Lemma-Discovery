module Tp = struct
  type t =
    | Bool
    | Int
    | IntList
    | IntTree
    | IntTreeI
    | IntTreeB

  type tpedvar = t * string

  let layout = function
    | Bool -> "bool"
    | Int -> "int"
    | IntList -> "int list"
    | IntTree -> "int tree"
    | IntTreeI -> "int treei"
    | IntTreeB -> "int treeb"

  let layouttvar (t, name) = (layout t) ^ ":" ^ name

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

  open Yojson.Basic
  let encode = function
    | Bool -> `String "B"
    | Int -> `String "I"
    | IntList -> `String "IL"
    | IntTree -> `String "IT"
    | IntTreeI -> `String "ITI"
    | IntTreeB -> `String "ITB"
  let decode json =
    let open Util in
    let tp = to_string json in
    if String.equal "B" tp then Bool
    else if String.equal "I" tp then Int
    else if String.equal "IL" tp then IntList
    else if String.equal "IT" tp then IntTree
    else if String.equal "ITI" tp then IntTreeI
    else if String.equal "ITB" tp then IntTreeB
    else raise @@ InterExn "Lit.Tree::decode wrong type"

  let tpedvar_encode (tp, name) =
    `Assoc ["t", `String "tpv";
            "tp", encode tp;
            "n", `String name]

  let tpedvar_decode json =
    let open Util in
    let treetp = json |> member "t" |> to_string in
    if String.equal "tpv" treetp then
      let tp = json |> member "tp" |> decode in
      let name = json |> member "n" |> to_string in
      (tp, name)
    else raise @@ InterExn (Printf.sprintf "%s::decode wrong type" "tpedvar")

  let tpedvar_eq (tp1, name1) (tp2, name2) =
    (eq tp1 tp2) && (String.equal name1 name2)
end
