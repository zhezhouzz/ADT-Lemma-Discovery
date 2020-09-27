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
  type spec = (string list) * E.forallformula
  val layout: t -> string
  val vc_layout: t -> string
  val layout_spec: spec -> string
  val layout_spec_entry: string -> spec -> string
  val eq: t -> t -> bool
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
  type spec = (string list) * E.forallformula
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
  let vc_layout a =
    let mk_indent indent = String.init indent (fun _ -> ' ') in
    let rec aux indent = function
      | ForAll _ -> raise @@ InterExn "vc does not involve forall"
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
  let layout_spec (args, formula) =
    sprintf "fun %s -> %s" (List.to_string (fun x -> x) args) (E.layout_forallformula formula)

  let layout_spec_entry name (args, formula) =
    sprintf "%s(%s):=\n%s" name
      (List.to_string (fun x -> x) args) (E.pretty_layout_forallformula formula)

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

end
