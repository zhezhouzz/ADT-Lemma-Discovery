module type EprTree = sig
  module SE: SimpleExpr.SimpleExpr
  type t =
    | True
    | Atom of SE.t
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
  type free_variable = string
  type forallformula = free_variable list * t
  val layout: t -> string
  val layout_forallformula: forallformula -> string
  val pretty_layout_forallformula: forallformula -> string
  val substm: SE.t Utils.StrMap.t -> t -> t
  val subst: t -> string list -> SE.t list -> t
  val subst_forallformula: forallformula -> string list -> SE.t list -> forallformula
  val eq: t -> t -> bool
  val eq_forallformula: forallformula -> forallformula -> bool
end

module EprTree(SE: SimpleExpr.SimpleExpr) : EprTree
  with type SE.L.t = SE.L.t
  with type SE.tp = SE.tp
  with type SE.t = SE.t = struct
  module SE = SE
  open Utils
  open Printf

  type t =
    | True
    | Atom of SE.t
    | Implies of t * t
    | Ite of t * t * t
    | Not of t
    | And of t list
    | Or of t list
    | Iff of t * t
  type free_variable = string
  type forallformula = free_variable list * t

  let rec layout = function
    | True -> "true"
    | Atom bexpr -> sprintf "(%s)" (SE.layout bexpr)
    | Implies (p1, p2) -> sprintf "(%s => %s)" (layout p1) (layout p2)
    | And ps -> List.inner_layout (List.map layout ps) "/\\" "true"
    | Or ps -> List.inner_layout (List.map layout ps) "\\/" "true"
    | Not p -> "~"^(layout p)
    | Iff (p1, p2) -> sprintf "(%s <=> %s)" (layout p1) (layout p2)
    | Ite (p1, p2, p3) ->
      sprintf "(ite %s %s %s)" (layout p1) (layout p2) (layout p3)

  let pretty_layout indent e =
    let mk_indent indent = String.init indent (fun _ -> ' ') in
    let rec aux indent = function
      | True -> "true"
      | Atom bexpr -> sprintf "%s%s" (mk_indent indent) (SE.layout bexpr)
      | Implies (Atom e1, Atom e2) ->
        sprintf "%s(%s => %s)"
          (mk_indent indent) (aux 0 (Atom e1)) (aux 0 (Atom e2))
      | Implies (p1, p2) ->
        sprintf "%s(\n%s => \n%s\n%s)"
          (mk_indent indent) (aux (indent + 1) p1) (aux (indent + 1) p2) (mk_indent indent)
      | And [] -> raise @@ InterExn "epr does not involve void conj"
      | And [p] -> aux indent p
      | And [Atom e1; Atom e2] -> sprintf "%s(%s /\\ %s)"
                                    (mk_indent indent) (aux 0 (Atom e1)) (aux 0 (Atom e2))
      | And [Atom e1; Atom e2; Atom e3] ->
        sprintf "%s(%s /\\ %s /\\ %s)"
          (mk_indent indent) (aux 0 (Atom e1)) (aux 0 (Atom e2)) (aux 0 (Atom e3))
      | And ps -> sprintf "%s(\n%s\n%s)" (mk_indent indent)
                    (List.inner_layout (List.map (aux (indent + 1)) ps) " /\\\n" "true")
                    (mk_indent indent)
      | Or [] -> raise @@ InterExn "epr does not involve void disconj"
      | Or [p] -> aux indent p
      | Or [Atom e1; Atom e2] -> sprintf "%s(%s \\/ %s)"
                                   (mk_indent indent)(aux 0 (Atom e1)) (aux 0 (Atom e2))
      | Or [Atom e1; Atom e2; Atom e3] ->
        sprintf "%s(%s \\/ %s \\/ %s)"
          (mk_indent indent) (aux 0 (Atom e1)) (aux 0 (Atom e2)) (aux 0 (Atom e3))
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
    in
    aux indent e

  let pretty_layout_forallformula (forallvars, body) =
    if (List.length forallvars) == 0 then layout body else
      sprintf "forall %s,%s" (List.inner_layout forallvars " " "") (pretty_layout 0 body)

  let layout_forallformula (forallvars, body) =
    if (List.length forallvars) == 0 then layout body else
      sprintf "forall %s,%s" (List.inner_layout forallvars " " "") (layout body)

  let subst body args argsvalue =
    let rec aux = function
      | True -> True
      | Atom bexpr -> Atom (SE.subst bexpr args argsvalue)
      | Implies (p1, p2) -> Implies (aux p1, aux p2)
      | And ps -> And (List.map aux ps)
      | Or ps -> Or (List.map aux ps)
      | Not p -> Not (aux p)
      | Iff (p1, p2) -> Iff (aux p1, aux p2)
      | Ite (p1, p2, p3) -> Ite (aux p1, aux p2, aux p3)
    in
    aux body

  let substm m body =
    let args, argsvalue =
      StrMap.fold (fun name v (args, argsvalue) ->
          name::args, v::argsvalue) m ([], []) in
    subst body args argsvalue

  let subst_forallformula (fv, body) args argsvalue =
    fv, subst body args argsvalue

  let eq a b =
    let rec aux a b =
      match (a, b) with
      | True, True -> true
      | Atom expr1, Atom expr2 -> SE.eq expr1 expr2
      | Implies (p1, p2), Implies (p1', p2') -> (aux p1 p1') && (aux p2 p2')
      | And ps1, And ps2 -> List.for_all2 aux ps1 ps2
      | Or ps1, Or ps2 -> List.for_all2 aux ps1 ps2
      | Not p1, Not p2 -> aux p1 p2
      | Iff (p1, p2), Iff (p1', p2') -> (aux p1 p1') && (aux p2 p2')
      | Ite (p1, p2, p3), Ite (p1', p2', p3') -> (aux p1 p1') && (aux p2 p2') && (aux p3 p3')
      | _ -> false
    in
    aux a b

  let eq_forallformula (fv1, body1) (fv2, body2) =
    (List.for_all2 String.equal fv1 fv2) && (eq body1 body2)
end
