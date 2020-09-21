module type Epr = sig
  include EprTree.EprTree
  type value = SE.value
  val fv: t -> string list
  val type_check : t -> (t * bool)
  val exec: t -> value Utils.StrMap.t -> bool
  val forallformula_exec: forallformula -> value Utils.StrMap.t -> bool
  val to_z3: Z3.context -> t -> Z3.Expr.expr
  val forallformula_to_z3: Z3.context -> forallformula -> Z3.Expr.expr
  val neg_forallf: forallformula -> string list * forallformula
  val related_dt: t -> string list -> string list
  val desugar: t -> t
  val to_nnf: t -> t
  val simplify_ite: t -> t
end

module Epr (E: EprTree.EprTree): Epr = struct
  include E
  open Utils
  type value = SE.value
  module V = Preds.Pred.Value
  let fv _ = []
  let type_check bexpr = (bexpr, true)
  let exec e env =
    let rec aux = function
      | True -> true
      | Atom bexpr ->
        (match SE.exec bexpr env with
         | V.B b -> b
         | _ -> raise @@ InterExn "not a bool value in epr"
        )
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
      | Atom b -> SE.extract_dt b
      | Implies (p1, p2) -> concat @@ List.map aux [p1;p2]
      | And ps -> concat @@ List.map aux ps
      | Or ps -> concat @@ List.map aux ps
      | Not p -> aux p
      | Iff (p1, p2) -> concat @@ List.map aux [p1;p2]
      | Ite (p1, p2, p3) -> concat @@ List.map aux [p1;p2;p3]
    in
    let dts, names = aux e in
    let names = List.remove_duplicates String.equal names in
    dts @ (List.map (fun n -> StrMap.find n env) names)

  let forallu e env =
    let dts = extract_dt e env in
    let us = List.concat @@ List.map V.flatten_forall dts in
    let us = List.remove_duplicates (fun x y -> x == y) us in
    match IntList.max_opt us with
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
          StrMap.add name (V.I value) m
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

  open Z3
  open Arithmetic
  open Z3aux

  let to_z3 ctx epr =
    let rec aux = function
      | True -> Boolean.mk_true ctx
      | Atom bexpr -> SE.to_z3 ctx bexpr
      | Implies (p1, p2) -> Boolean.mk_implies ctx (aux p1) (aux p2)
      | Ite (p1, p2, p3) -> Boolean.mk_ite ctx (aux p1) (aux p2) (aux p3)
      | Not p -> Boolean.mk_not ctx (aux p)
      | And ps -> Boolean.mk_and ctx (List.map aux ps)
      | Or ps -> Boolean.mk_or ctx (List.map aux ps)
      | Iff (p1, p2) -> Boolean.mk_iff ctx (aux p1) (aux p2) in
    aux epr
  let forallformula_to_z3 ctx (fv, epr) =
    let fv = List.map (fun name -> Integer.mk_const_s ctx name) fv in
    make_forall ctx fv (to_z3 ctx epr)
  let neg_forallf (fv, epr) = fv, ([], Not epr)
  let related_dt e fv =
    let rec aux = function
      | True -> []
      | Atom expr -> SE.related_dt expr fv
      | Implies (p1, p2) -> (aux p1) @ (aux p2)
      | Ite (p1, p2, p3) -> (aux p1) @ (aux p2) @ (aux p3)
      | Not p -> (aux p)
      | And ps -> List.flatten (List.map aux ps)
      | Or ps -> List.flatten (List.map aux ps)
      | Iff (p1, p2) -> (aux p1) @ (aux p2) in
    List.remove_duplicates String.equal (aux e)

  let desugar a =
    let rec aux = function
      | Atom se -> Atom se
      | Implies (p1, p2) -> aux (Or [Not p1; p2])
      | Ite (p1, p2, p3) -> aux (And [Implies (p1, p2); Implies (Not p1, p3)])
      | Not p -> Not (aux p)
      | And ps -> And (List.map aux ps)
      | Or ps -> Or (List.map aux ps)
      | Iff (p1, p2) -> aux (Or [And [p1; p2]; And [Not p1; Not p2]])
      | True -> True
    in
    aux a

  let to_nnf a =
    let rec aux a =
      match a with
      | Atom _ | True | Not (True) | Not (Atom _) -> a
      | Not (Not p) -> aux p
      | Not (And ps) -> Or (List.map (fun p -> aux (Not p)) ps)
      | Not (Or ps) -> And (List.map (fun p -> aux (Not p)) ps)
      | And ps -> And (List.map aux ps)
      | Or ps -> Or (List.map aux ps)
      | _ -> raise @@ InterExn "undesugar"
    in
    aux (desugar a)

  let simplify_ite a =
    let simp_ite p1 p2 p3 =
      match p2, p3 with
      | True, True -> True
      | True, Not True -> p1
      | True, p3 -> Or [p1; p3]
      | Not True, True -> Not p1
      | Not True, Not True -> Not True
      | Not True, p3 -> And [Not p1; p3]
      | p2, True -> Or [Not p1; p2]
      | p2, Not True -> And [p1; p2]
      | _ -> Ite (p1, p2, p3)
    in
    let rec aux a =
      match a with
      | Atom se -> Atom se
      | Implies (p1, p2) -> aux (Or [Not p1; p2])
      | Ite (p1, p2, p3) -> simp_ite (aux p1) (aux p2) (aux p3)
      | Not p -> Not (aux p)
      | And ps -> And (List.map aux ps)
      | Or ps -> Or (List.map aux ps)
      | Iff (p1, p2) -> Iff (aux p1, aux p2)
      | True -> True
    in
    aux a
end
