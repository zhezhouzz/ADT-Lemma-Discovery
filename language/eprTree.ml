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
  type free_variable = Tp.Tp.tpedvar
  type forallformula = free_variable list * t
  val layout: t -> string
  val layout_forallformula: forallformula -> string
  val pretty_layout_forallformula: forallformula -> string
  val pretty_layout_epr: t -> string
  val substm: SE.t Utils.StrMap.t -> t -> t
  val subst: t -> string list -> SE.t list -> t
  val subst_forallformula: forallformula -> string list -> SE.t list -> forallformula
  val eq: t -> t -> bool
  val eq_forallformula: forallformula -> forallformula -> bool
  val encode: t -> Yojson.Basic.t
  val decode: Yojson.Basic.t -> t
  val forallformula_encode: forallformula -> Yojson.Basic.t
  val forallformula_decode: Yojson.Basic.t -> forallformula
  val simplify_dt_result: t -> t
  val num_atom: t -> int
end

module EprTree(SE: SimpleExpr.SimpleExpr) : EprTree
  with type SE.L.t = SE.L.t
  with type SE.tp = SE.tp
  with type SE.t = SE.t = struct
  module SE = SE
  module T = Tp.Tp
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
  type free_variable = Tp.Tp.tpedvar
  type forallformula = free_variable list * t

  open Yojson.Basic
  let treetp_name = "E"
  let encode_field = encode_field_ treetp_name
  let decode_field = decode_field_ treetp_name
  let rec encode = function
    | True -> encode_field "ETrue" (`List [])
    | Atom bexpr -> encode_field "EAtom" (`List [SE.encode bexpr])
    | Implies (p1, p2) -> encode_field "EImplies" (`List [encode p1; encode p2])
    | And ps -> encode_field "EAnd" (`List (List.map encode ps))
    | Or ps -> encode_field "EOr" (`List (List.map encode ps))
    | Not p -> encode_field "ENot" (`List [encode p])
    | Iff (p1, p2) -> encode_field "EIff" (`List [encode p1; encode p2])
    | Ite (p1, p2, p3) -> encode_field "EIte" (`List [encode p1; encode p2; encode p3])
  let rec decode json =
    let e = InterExn (Printf.sprintf "%s::decode wrong field" treetp_name) in
    let field, value = decode_field json in
    match field, value with
    | field, `List [] when String.equal "ETrue" field -> True
    | field, `List [bexpr] when String.equal "EAtom" field -> Atom (SE.decode bexpr)
    | field, `List [p1;p2] when String.equal "EImplies" field ->
      Implies (decode p1, decode p2)
    | field, `List ps when String.equal "EAnd" field -> And (List.map decode ps)
    | field, `List ps when String.equal "EOr" field -> Or (List.map decode ps)
    | field, `List [p] when String.equal "ENot" field -> Not (decode p)
    | field, `List [p1;p2] when String.equal "EIff" field -> Iff (decode p1, decode p2)
    | field, `List [p1;p2;p3] when String.equal "EIte" field ->
      Ite (decode p1, decode p2, decode p3)
    | _ -> raise e

  let forallformula_tpname = "ff"

  let forallformula_encode (qv, body) =
    `Assoc ["treetp", `String forallformula_tpname;
            "qv", `List (List.map T.tpedvar_encode qv);
            "body", encode body]

  let forallformula_decode json =
    let e = InterExn (Printf.sprintf "%s::decode wrong type" forallformula_tpname) in
    let open Util in
    let treetp = json |> member "treetp" |> to_string in
    if String.equal forallformula_tpname treetp then
      let qv =
        match json |> member "qv" with
        | `List qv -> List.map T.tpedvar_decode qv
        | _ -> raise e
      in
      let body = json |> member "body" |> decode in
      (qv, body)
    else raise e

  (* let sym_and = "/\\"
   * let sym_or = "\\/"
   * let sym_not = "~"
   * let sym_implies = "=>"
   * let sym_iff = "<=>" *)

  let sym_and = "&&"
  let sym_or = "||"
  let sym_not = "!"
  let sym_implies = "==>"
  let sym_iff = "<==>"

  let rec layout = function
    | True -> "true"
    | Atom bexpr -> sprintf "(%s)" (SE.layout bexpr)
    | Implies (p1, p2) -> sprintf "(%s %s %s)" (layout p1) sym_implies (layout p2)
    | And ps -> sprintf "(%s)" (List.inner_layout (List.map layout ps) sym_and "true")
    | Or ps -> sprintf "(%s)" (List.inner_layout (List.map layout ps) sym_or "false")
    | Not p -> sprintf "(%s)" (sym_not^(layout p))
    | Iff (p1, p2) -> sprintf "(%s %s %s)" (layout p1) sym_iff (layout p2)
    | Ite (p1, p2, p3) ->
      sprintf "(ite %s %s %s)" (layout p1) (layout p2) (layout p3)

  let pretty_layout indent e =
    let mk_indent indent = String.init indent (fun _ -> ' ') in
    let rec aux indent = function
      | True -> "true"
      | Atom bexpr -> sprintf "%s%s" (mk_indent indent) (SE.layout bexpr)
      | Implies (Atom e1, Atom e2) ->
        sprintf "%s(%s %s %s)"
          (mk_indent indent) (aux 0 (Atom e1)) sym_implies (aux 0 (Atom e2))
      | Implies (p1, p2) ->
        sprintf "%s(\n%s %s \n%s\n%s)"
          (mk_indent indent) (aux (indent + 1) p1) sym_implies
          (aux (indent + 1) p2) (mk_indent indent)
      | And [] -> raise @@ InterExn "epr does not involve void conj"
      | And [p] -> aux indent p
      | And [Atom e1; Atom e2] ->
        sprintf "%s(%s %s %s)" (mk_indent indent) (aux 0 (Atom e1)) sym_and (aux 0 (Atom e2))
      | And [Atom e1; Atom e2; Atom e3] ->
        sprintf "%s(%s %s %s %s %s)"
          (mk_indent indent) (aux 0 (Atom e1)) sym_and
          (aux 0 (Atom e2)) sym_and (aux 0 (Atom e3))
      | And ps -> sprintf "%s(\n%s\n%s)" (mk_indent indent)
                    (List.inner_layout (List.map (aux (indent + 1)) ps) (" "^sym_and^"\n") "true")
                    (mk_indent indent)
      | Or [] -> raise @@ InterExn "epr does not involve void disconj"
      | Or [p] -> aux indent p
      | Or [Atom e1; Atom e2] ->
        sprintf "%s(%s %s %s)" (mk_indent indent)(aux 0 (Atom e1)) sym_or (aux 0 (Atom e2))
      | Or [Atom e1; Atom e2; Atom e3] ->
        sprintf "%s(%s %s %s %s %s)"
          (mk_indent indent) (aux 0 (Atom e1))
          sym_or (aux 0 (Atom e2)) sym_or (aux 0 (Atom e3))
      | Or ps -> sprintf "%s(\n%s\n%s)" (mk_indent indent)
                   (List.inner_layout (List.map (aux (indent + 1)) ps) (" "^sym_or^"\n") "false")
                   (mk_indent indent)
      | Not p -> sprintf "%s%s%s" (mk_indent indent) sym_not (aux 0 p)
      | Iff (p1, p2) ->
        sprintf "%s(%s %s \n%s)"
          (mk_indent indent) (aux 0 p1) sym_iff (aux (indent + 1) p2)
      | Ite (p1, p2, p3) ->
        sprintf "%s(ite%s\n%s\n%s)"
          (mk_indent indent) (aux 1 p1) (aux (indent + 4) p2) (aux (indent + 4) p3)
    in
    aux indent e

  let pretty_layout_forallformula (forallvars, body) =
    let qvstr = List.map T.layouttvar forallvars in
    if (List.length forallvars) == 0 then layout body else
      sprintf "forall %s,%s" (List.inner_layout qvstr " " "") (pretty_layout 0 body)

  let pretty_layout_epr t = pretty_layout 0 t

  let layout_forallformula (forallvars, body) =
    let qvstr = List.map T.layouttvar forallvars in
    if (List.length forallvars) == 0 then layout body else
      sprintf "forall %s,%s" (List.inner_layout qvstr " " "") (layout body)

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

  let simplify_eq body =
    let eq_subst body x y =
      let x =
        match x with
        | SE.Var (_, name) -> [name]
        | _ -> raise @@ InterExn "epr simplify_eq"
      in
      let y = [y] in
      subst body x y
    in
    let rec aux body =
      match body with
      | True | Atom _ | Not _ -> body
      | Implies (p1, p2) -> Implies (aux p1, aux p2)
      | And ps -> And (List.map aux ps)
      | Or ps -> Or (List.map aux ps)
      | Iff (p1, p2) -> Iff (aux p1, aux p2)
      | Ite (p1, p2, p3) ->
        (match p1 with
         | Atom (SE.Op (_, op, [x;y])) when String.equal op "=="->
           (* let _ = printf "subst[%s -> %s]\n" (SE.layout x) (SE.layout y) in *)
           Ite (p1, aux (eq_subst p2 x y), aux p3)
         | _ -> Ite (p1, aux p2, aux p3)
        )
    in
    aux body

  let prune body =
    let rec aux pos neg body =
      match body with
      | True | Not True -> body
      | Not _ -> raise @@ InterExn "ast:prune"
      | Atom se ->
        if List.exists (fun se' -> SE.eq se se') pos then True
        else if List.exists (fun se' -> SE.eq se se') neg then Not True
        else body
      | Implies (_, _) | And _ | Or _ | Iff (_, _) -> raise @@ InterExn "ast:prune"
      | Ite (p1, p2, p3) ->
        (match aux pos neg p1 with
        | True -> aux pos neg p2
        | Not True -> aux pos neg p3
        | Atom p1' ->
          (match aux (p1' :: pos) neg p2, aux pos (p1' :: neg) p3 with
           | True, True -> True
           | Not True, Not True -> Not True
           | True, Not True -> Atom p1'
           | Not True, True -> Not (Atom p1')
           | True, p3' -> Or [Atom p1'; p3']
           | Not True, p3' -> And [Not (Atom p1'); p3']
           | p2', True -> Or [Not (Atom p1'); p2';]
           | p2', Not True -> And [Atom p1'; p2']
           | p2', p3' -> Ite (Atom p1', p2', p3')
          )
        | _ -> raise @@ InterExn "ast:prune"
        )
    in
    aux [] [] body

  let simplify_dt_result body =
    (* let _ = printf "before:\n%s\n" (pretty_layout_epr body) in *)
    let result = prune @@ simplify_eq body in
    (* let _ = printf "end:\n%s\n" (pretty_layout_epr result) in *)
    result

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
    let _, fv1str = List.split fv1 in
    let _, fv2str = List.split fv2 in
    (List.for_all2 String.equal fv1str fv2str) && (eq body1 body2)

  let num_atom a =
    let rec aux = function
      | True -> 1
      | Atom _ -> 1
      | Implies (p1, p2) -> (aux p1) + (aux p2)
      | And ps -> List.fold_left (fun sum p -> (aux p) + sum) 0 ps
      | Or ps -> List.fold_left (fun sum p -> (aux p) + sum) 0 ps
      | Not p -> aux p
      | Iff (p1, p2) -> (aux p1) + (aux p2)
      | Ite (p1, p2, p3) ->(aux p1) + (aux p2) + (aux p3)
    in
    aux a

  (* let is_lit = function
   *   | Not (Atom _) | Atom _ -> true
   *   | _ -> false
   * 
   * let to_clauses (qv, body) =
   *   let rec aux prefix = function
   *     | True | Not True -> raise @@ InterExn "never happen in to_clauses"
   *     | Not (Atom _) as p -> prefix, p
   *     | Atom _ as p -> prefix, p
   *     | Not _ -> raise @@ InterExn "never happen in to_clauses"
   *     | Implies (_, _) -> raise @@ InterExn "never happen in to_clauses"
   *     | And ps ->
   *       if List.for_all is_lit ps then 
   *       else raise @@ InterExn "never happen in to_clauses"
   *     | Or ps -> List.fold_left (fun sum p -> (aux p) + sum) 0 ps
   *     | Not p -> aux p
   *     | Iff (p1, p2) -> (aux p1) + (aux p2)
   *     | Ite (p1, p2, p3) ->(aux p1) + (aux p2) + (aux p3)
   *   in
   *   aux a *)
end
