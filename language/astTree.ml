module type AstTree = sig
  module E: Epr.Epr
  type t =
    | ForAll of E.forallformula
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
    | SpecApply of string * E.SE.t list
  type spec = (Tp.Tp.tpedvar list) * E.forallformula
  val layout: t -> string
  val vc_layout: t -> string
  val layout_spec: spec -> string
  val layout_spec_entry: string -> spec -> string
  val eq: t -> t -> bool
  val get_app_args: t -> string -> E.SE.t list list
  val neg_spec: string -> t -> t
  val implies_to_and: t -> t
end

module AstTree (E: Epr.Epr) : AstTree
  with type E.SE.L.t = E.SE.L.t
  with type E.SE.tp = E.SE.tp
  with type E.SE.t = E.SE.t
  with type E.t = E.t = struct
  module E = E
  open Utils
  open Printf
  type t =
    | ForAll of E.forallformula
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
    | SpecApply of string * E.SE.t list
  type spec = (Tp.Tp.tpedvar list) * E.forallformula
  let rec layout = function
    | ForAll ff -> E.layout_forallformula ff
    | Implies (p1, p2) -> sprintf "(%s => %s)" (layout p1) (layout p2)
    | And ps -> sprintf "(%s)" (List.inner_layout (List.map layout ps) "∧" "true")
    | Or ps -> sprintf "(%s)" (List.inner_layout (List.map layout ps) "∨" "true")
    | Not p -> "~"^(layout p)
    | Iff (p1, p2) -> sprintf "(%s <=> %s)" (layout p1) (layout p2)
    | Ite (p1, p2, p3) ->
      sprintf "(ite %s %s %s)" (layout p1) (layout p2) (layout p3)
    | SpecApply (specname, args) ->
      sprintf "%s(%s)" specname (List.to_string E.SE.layout args)

  let neg_spec name ast =
    let rec aux = function
    | ForAll _ -> raise @@ InterExn "never happen aux"
    | Implies (p1, p2) -> Implies (aux p1, aux p2)
    | And ps -> And (List.map aux ps)
    | Or ps -> Or (List.map aux ps)
    | Not _ -> raise @@ InterExn "never happen aux"
    | Iff (_, _) -> raise @@ InterExn "never happen aux"
    | Ite (_, _, _) -> raise @@ InterExn "never happen aux"
    | SpecApply (specname, args) ->
      if String.equal specname name
      then And [Not (SpecApply (specname, args)); SpecApply ("co_" ^ specname, args)]
      else SpecApply (specname, args)
    in
    aux ast

  let implies_to_and ast =
    let rec aux = function
      | ForAll _ -> raise @@ InterExn "never happen aux"
      | Implies (p1, p2) -> And [aux p1; aux p2]
      | And ps -> And (List.map aux ps)
      | Or ps -> Or (List.map aux ps)
      | Not (SpecApply (specname, args)) -> Not (SpecApply (specname, args))
      | Not _ -> raise @@ InterExn "never happen aux"
      | Iff (_, _) -> raise @@ InterExn "never happen aux"
      | Ite (_, _, _) -> raise @@ InterExn "never happen aux"
      | SpecApply (specname, args) -> SpecApply (specname, args)
    in
    aux ast

  let vc_layout a =
    let mk_indent indent = String.init indent (fun _ -> ' ') in
    let rec aux indent = function
      | ForAll ff -> sprintf "%s%s" (mk_indent indent) (E.pretty_layout_forallformula ff)
      | Implies (SpecApply (n1, args1), SpecApply (n2, args2)) ->
        sprintf "%s(%s => %s)"
          (mk_indent indent)
          (aux 0 (SpecApply (n1, args1))) (aux 0 (SpecApply (n2, args2)))
      | Implies (p1, p2) ->
        sprintf "%s(%s => \n%s\n%s)"
          (mk_indent indent) (aux 0 p1) (aux (indent + 1) p2) (mk_indent indent)
      | And [] -> raise @@ InterExn "vc does not involve void conj"
      | And [p] -> aux indent p
      | And [SpecApply (n1, args1); SpecApply (n2, args2)] ->
        sprintf "%s(%s /\\ %s)" (mk_indent indent)
          (aux 0 (SpecApply (n1, args1))) (aux 0 (SpecApply (n2, args2)))
      | And ps -> sprintf "%s(\n%s\n%s)" (mk_indent indent)
                    (List.inner_layout (List.map (aux (indent + 1)) ps) " /\\\n" "true")
                    (mk_indent indent)
      | Or [] -> raise @@ InterExn "vc does not involve void disconj"
      | Or [p] -> aux indent p
      | Or [SpecApply (n1, args1); SpecApply (n2, args2)] ->
        sprintf "%s(%s \\/ %s)" (mk_indent indent)
          (aux 0 (SpecApply (n1, args1))) (aux 0 (SpecApply (n2, args2)))
      | Or ps -> sprintf "%s(\n%s\n%s)" (mk_indent indent)
                   (List.inner_layout (List.map (aux (indent + 1)) ps) " \\/\n" "false")
                   (mk_indent indent)
      | Not p -> sprintf "%s~%s" (mk_indent indent) (aux 0 p)
      | Iff (p1, p2) ->
        sprintf "%s(%s <=> \n%s)"
          (mk_indent indent) (aux 0 p1) (aux (indent + 1) p2)
      | Ite (p1, p2, p3) ->
        sprintf "%s(ite%s\n%s\n%s)"
          (mk_indent indent) (aux 1 p1) (aux (indent + 4) p2) (aux (indent + 4) p3)
      | SpecApply (specname, args) ->
        sprintf "%s%s(%s)" (mk_indent indent) specname (List.to_string E.SE.layout args)
    in
    aux 0 a

  module T = Tp.Tp
  let layout_spec (args, formula) =
    sprintf "fun %s -> %s" (List.to_string T.layouttvar args)
      (E.pretty_layout_forallformula formula)

  let layout_spec_entry name (args, formula) =
    sprintf "%s(%s):=\n%s" name
      (List.to_string T.layouttvar args) (E.pretty_layout_forallformula formula)

  let eq a b =
    let rec aux a b =
      match (a, b) with
      | ForAll ff1, ForAll ff2 -> E.eq_forallformula ff1 ff2
      | Implies (p1, p2), Implies (p1', p2') -> (aux p1 p1') && (aux p2 p2')
      | And ps1, And ps2 -> List.for_all2 aux ps1 ps2
      | Or ps1, Or ps2 -> List.for_all2 aux ps1 ps2
      | Not p1, Not p2 -> aux p1 p2
      | Iff (p1, p2), Iff (p1', p2') -> (aux p1 p1') && (aux p2 p2')
      | Ite (p1, p2, p3), Ite (p1', p2', p3') -> (aux p1 p1') && (aux p2 p2') && (aux p3 p3')
      | SpecApply (specname1, args1), SpecApply (specname2, args2) ->
        (String.equal specname1 specname2) &&
        (List.for_all2 E.SE.eq args1 args2)
      | _ -> false
    in
    aux a b

  let get_app_args t specname =
    let rec aux t res =
      match t with
      | ForAll _ -> raise @@ InterExn "bad in get_app_args"
      | Implies (p1, p2) -> aux p2 (aux p1 res)
      | And ps -> List.fold_left (fun r p -> aux p r) res ps
      | Or ps -> List.fold_left (fun r p -> aux p r) res ps
      | Not p -> aux p res
      | Iff (p1, p2) -> aux p2 (aux p1 res)
      | Ite (p1, p2, p3) -> aux p3 (aux p2 (aux p1 res))
      | SpecApply (specname', args) ->
        if String.equal specname specname' then
          args :: res
        else
          res
    in
    aux t []
end
