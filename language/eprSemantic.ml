module type EprSemantic = sig
  include Epr.Epr
  type value
  val fv: t -> string list
  val type_check : t -> (t * bool)
  val exec: t -> value Utils.StrMap.t -> bool
  val spec_exec: spec -> value Utils.StrMap.t -> bool
  val flatten_forall: value -> int list
end

module EprSemantic (E: Epr.Epr) (Elem: Preds.Elem.Elem)
    (BS: BexprSemantic.BexprSemantic
     with type value = Elem.t
     with type L.t = E.B.L.t
     with type tp = E.B.tp
     with type t = E.B.t):
  EprSemantic with type value = BS.value = struct
  include E
  open Utils
  type value = BS.value
  let fv _ = []
  let type_check bexpr = (bexpr, true)
  let exec e env =
    let rec aux = function
      | True -> true
      | Atom bexpr -> BS.exec bexpr env
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
      | Atom b -> BS.extract_dt b
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
    match intlist_max us with
    | None -> 0 :: us
    | Some m -> (m + 1) :: us

  (* TODO *)
  let spec_exec (_, e) env = 0 > (List.length (forallu e env))
end
