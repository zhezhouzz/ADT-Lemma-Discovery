module type Epr = sig
  include EprTree.EprTree
  type value = B.value
  val fv: t -> string list
  val type_check : t -> (t * bool)
  val exec: t -> value Utils.StrMap.t -> bool
  val forallformula_exec: forallformula -> value Utils.StrMap.t -> bool
  val flatten_forall: value -> int list
end

module Epr (E: EprTree.EprTree): Epr = struct
  include E
  open Utils
  type value = B.value
  module Elem = Preds.Pred.Element
  let fv _ = []
  let type_check bexpr = (bexpr, true)
  let exec e env =
    let rec aux = function
      | True -> true
      | Atom bexpr -> B.exec bexpr env
      | Implies (e1, e2) -> if aux e1 then aux e2 else true
      | Ite (e1, e2, e3) -> if aux e1 then aux e2 else aux e3
      | Not e -> not (aux e)
      | And l -> List.for_all (fun x -> x) @@ List.map aux l
      | Or l -> List.exists (fun x -> x) @@ List.map aux l
      | Iff (e1, e2) -> (aux e1) == (aux e2)
    in
    aux e
  let extract_dt e env =
    let concat l =
      let la, lb = List.split l in
      (List.concat la, List.concat lb)
    in
    let rec aux = function
      | True -> [], []
      | Atom b -> B.extract_dt b
      | Implies (p1, p2) -> concat @@ List.map aux [p1;p2]
      | And ps -> concat @@ List.map aux ps
      | Or ps -> concat @@ List.map aux ps
      | Not p -> aux p
      | Iff (p1, p2) -> concat @@ List.map aux [p1;p2]
      | Ite (p1, p2, p3) -> concat @@ List.map aux [p1;p2;p3]
    in
    let dts, names = aux e in
    let names = remove_duplicates String.equal names in
    dts @ (List.map (fun n -> StrMap.find n env) names)

  let flatten_forall = function
    | Elem.I _ | Elem.B _ | Elem.NotADt -> raise @@ InterExn "flatten_forall: not a datatype"
    | Elem.L il -> list_flatten_forall (fun x y -> x == y) il
    | Elem.T it -> tree_flatten_forall (fun x y -> x == y) it

  let forallu e env =
    let dts = extract_dt e env in
    let us = List.concat @@ List.map flatten_forall dts in
    let us = remove_duplicates (fun x y -> x == y) us in
    match intlist_max us with
    | None -> 0 :: us
    | Some m -> (m + 1) :: us

  let forallformula_exec (fv, e) env =
    let us = forallu e env in
    (* let _ = Printf.printf "%s\n" (intlist_to_string us) in *)
    let len = List.length us in
    let ids = List.init (List.length fv) (fun _ -> 0) in
    let rec next = function
      | [] -> None
      | h :: t ->
        if len == (h + 1) then
          match next t with
          | None -> None
          | Some t -> Some (0 :: t)
        else
          Some ((h + 1) :: t)
    in
    let rec aux ids =
      let us = List.map (fun x -> List.nth us x) ids in
      let us = List.combine fv us in
      let env = List.fold_left (fun m (name, value) ->
          StrMap.add name (Elem.I value) m
        ) env us in
      let _ = Printf.printf "assign free variables: %s\n"
          (List.fold_left (fun str (name, v) ->
               Printf.sprintf "%s%s=%i;" str name v)
          "" us) in
      if exec e env then
        match next ids with
        | None -> true
        | Some ids -> aux ids
      else false
    in
    aux ids
end
