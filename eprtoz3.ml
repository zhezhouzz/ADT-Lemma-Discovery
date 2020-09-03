open Utils
open Printf
open Epr
open Atom
open Z3
open Arithmetic
open Z3aux
open Atomtoz3

let tp_to_sort ctx = function
  | Int -> Integer.mk_sort ctx
  | Bool -> Boolean.mk_sort ctx
  | Dt -> Integer.mk_sort ctx

let to_z3_ ctx e =
  let rec aux = function
  | True -> Boolean.mk_true ctx
  | Atom bexpr -> bexpr_to_z3 ctx bexpr
  | Implies (p1, p2) -> Boolean.mk_implies ctx (aux p1) (aux p2)
  | And ps -> Boolean.mk_and ctx (List.map aux ps)
  | Or ps -> Boolean.mk_or ctx (List.map aux ps)
  | Not p -> Boolean.mk_not ctx (aux p)
  | Ite (p1, p2, p3) -> Boolean.mk_ite ctx (aux p1) (aux p2) (aux p3)
  | Iff (p1, p2) -> Boolean.mk_iff ctx (aux p1) (aux p2)
  | BApp (fname, args) -> raise @@ ZZExn "to_z3: undefined"
	| Forall (globarvars, body) ->
   let globarvars = List.map (var_to_z3 ctx) globarvars in
   make_forall ctx globarvars (aux body)
  in
  aux e

let subst name value e =
  let rec aux = function
    | True -> True
    | Atom b -> Atom (subst_bexpr name value b)
    | Implies (p1, p2) -> Implies (aux p1, aux p2)
    | And ps -> And (List.map aux ps)
    | Or ps -> Or (List.map aux ps)
    | Not p -> Not (aux p)
    | Ite (p1, p2, p3) -> Ite (aux p1, aux p2, aux p3)
    | Iff (p1, p2) -> Iff (aux p1, aux p2)
    | BApp (fname, args) -> BApp (fname, List.map (subst_aexpr name value) args)
    | Forall (_, _) -> raise @@ ZZExn "subst: undefined"
  in
  aux e

let spec_to_z3 ctx (name, args, globarvars, body) =
  let globarvars = List.map (var_to_z3 ctx) globarvars in
  let args = List.map (var_to_z3 ctx) args in
  let tps = List.init (List.length args) (fun _ -> Integer.mk_sort ctx) in
  let f = FuncDecl.mk_func_decl_s ctx name tps (Boolean.mk_sort ctx) in
  let left = FuncDecl.apply f args in
  let body = to_z3_ ctx body in
  let right = make_forall ctx globarvars body in
  (make_forall ctx args (Boolean.mk_eq ctx left right))

let spec_apply (_, args, globarvars, body) args' =
  let body = List.fold_left
      (fun e (n,v) -> subst n v e) body (List.combine args args') in
  Forall (globarvars, body)

let reduce e specs =
  let rec aux = function
    | True -> True
    | Atom bexpr -> Atom bexpr
    | Implies (p1, p2) -> Implies (aux p1, aux p2)
    | And ps -> And (List.map aux ps)
    | Or ps -> Or (List.map aux ps)
    | Not p -> Not (aux p)
    | Ite (p1, p2, p3) -> Ite (aux p1, aux p2, aux p3)
    | Iff (p1, p2) -> Iff (aux p1, aux p2)
    | BApp (fname, args) ->
      (match List.find_opt (fun (name,_,_,_) -> String.equal name fname) specs with
       | None -> raise @@ ZZExn "reduce error"
       | Some spec -> spec_apply spec args
      )
    | Forall (_, _) -> raise @@ ZZExn "reduce: undefined"
  in
  aux e

let to_z3 ctx client specs =
  let client = reduce client specs in
  to_z3_ ctx client

let axiom ctx = Boolean.mk_and ctx [axiom_next_link ctx; axiom_distinct ctx]
