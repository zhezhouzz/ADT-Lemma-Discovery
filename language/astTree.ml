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
  type let_binding = t option * Tp.Tp.tpedvar list
  val layout: t -> string
  val vc_layout: t -> string
  val layout_spec: spec -> string
  val print_spectable: spec Utils.StrMap.t -> unit
  val layout_spec_entry: string -> spec -> string
  val eq: t -> t -> bool
  val get_app_args: t -> string -> E.SE.t list list
  val neg_spec: string -> t -> t
  val implies_to_and: t -> t
  val merge_and: t -> t
  val make_match: Tp.Tp.tpedvar list -> Tp.Tp.tpedvar list ->
    (let_binding * let_binding) list -> t
  val to_dnf: t -> t list
  val encode: t -> Yojson.Basic.t
  val decode: Yojson.Basic.t -> t
  val spec_encode: spec -> Yojson.Basic.t
  val spec_decode: Yojson.Basic.t -> spec
  val spectable_eq: spec Utils.StrMap.t -> spec Utils.StrMap.t -> bool
  val spectable_encode: spec Utils.StrMap.t -> Yojson.Basic.t
  val spectable_decode: Yojson.Basic.t -> spec Utils.StrMap.t
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

  let merge_and a =
    let rec get_and = function
      | ForAll _ | Or _ | Not _ | Iff (_, _) | Ite (_, _, _) ->
        raise @@ InterExn "never happen in merge and"
      | And ps -> List.flatten (List.map get_and ps)
      | SpecApply (_, _) as a -> [a]
      | Implies (_, _) as a -> [a]
    in
    let rec aux = function
      | ForAll _ | Implies (_, _) | Not _ | Iff (_, _) | Ite (_, _, _) | SpecApply (_, _)->
        raise @@ InterExn "never happen in merge and"
      | Or ps -> Or (List.map aux ps)
      | And _ as a-> And (get_and a)
    in
    aux a

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

  let print_spectable spectable =
    StrMap.iter (fun name spec ->
        printf "%s\n" (layout_spec_entry name spec)
      ) spectable

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

  type let_binding = t option * Tp.Tp.tpedvar list

  let make_match
      (matched:Tp.Tp.tpedvar list) (target:Tp.Tp.tpedvar list)
      (branchs:(let_binding * let_binding) list) =
    let matched : E.SE.t list = List.map E.SE.from_tpedvar matched in
    let target : E.SE.t list = List.map E.SE.from_tpedvar target in
    let handle_case matched_vars (body, matched_vars') =
      let matched_vars' = List.map E.SE.from_tpedvar matched_vars' in
      let eq_specs = List.filter_map
          (fun (x, x') ->
             if E.SE.eq x x' then None else Some (SpecApply("equal", [x;x']))
          )
          (List.combine matched_vars matched_vars') in
      match body with
      | None -> eq_specs
      | Some body -> body :: eq_specs
    in
    let handle_banch (incase, outcase) =
      And ((handle_case matched incase) @ (handle_case target outcase))
    in
    (* let handle_banch (matched', target') =
     *   let ps = List.flatten @@
     *     List.map (fun (x, (t, x')) ->
     *         let x' = E.SE.from_tpedvar x' in
     *         let eq_spec = SpecApply("equal", [x;x']) in
     *         match t with
     *         | None -> [eq_spec]
     *         | Some t -> [t;eq_spec]
     *     ) (List.combine matched matched')
     *   in
     *   let qs = List.flatten @@
     *     List.map (fun (x, (t, x')) ->
     *         let x' = E.SE.from_tpedvar x' in
     *         let eq_spec = SpecApply("equal", [x;x']) in
     *         match t with
     *         | None -> [eq_spec]
     *         | Some t -> [t;eq_spec]
     *       ) (List.combine target target')
     *   in
     *   And (ps @ qs)
     * in *)
    Or (List.map handle_banch branchs)

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

  let to_dnf a =
    let rec aux a =
      match a with
      | SpecApply (_, _) -> [[a]]
      | Or ps -> List.concat @@ List.map aux ps
      | And ps -> List.map (fun l -> List.flatten l) (List.choose_list_list (List.map aux ps))
      | Implies (_,_) -> [[a]]
      | _ -> raise @@ InterExn (sprintf "to dnf(%s)" (layout a))
    in
    List.map (fun l -> And l) (aux a)

  open Yojson.Basic
  let treetp_name = "A"
  let encode_field = encode_field_ treetp_name
  let decode_field = decode_field_ treetp_name
  let rec encode = function
    | ForAll _ -> raise @@ InterExn "never happen ast encode"
    | Implies (p1, p2) -> encode_field "AImplies" (`List [encode p1; encode p2])
    | And ps -> encode_field "AAnd" (`List (List.map encode ps))
    | Or ps -> encode_field "AOr" (`List (List.map encode ps))
    | Not p -> encode_field "ANot" (`List [encode p])
    | Iff (p1, p2) -> encode_field "AIff" (`List [encode p1; encode p2])
    | Ite (p1, p2, p3) -> encode_field "AIte" (`List [encode p1; encode p2; encode p3])
    | SpecApply (specname, args) ->
      encode_field "ASpecApply"
        (`List [`String specname; `List (List.map E.SE.encode args)])
  let rec decode json =
    let e = InterExn (Printf.sprintf "%s::decode wrong field" treetp_name) in
    let field, value = decode_field json in
    match field, value with
    (* | field, _ when String.equal "Forall" field -> True *)
    | field, `List [p1;p2] when String.equal "AImplies" field ->
      Implies (decode p1, decode p2)
    | field, `List ps when String.equal "AAnd" field -> And (List.map decode ps)
    | field, `List ps when String.equal "AOr" field -> Or (List.map decode ps)
    | field, `List [p] when String.equal "ANot" field -> Not (decode p)
    | field, `List [p1;p2] when String.equal "AIff" field -> Iff (decode p1, decode p2)
    | field, `List [p1;p2;p3] when String.equal "AIte" field ->
      Ite (decode p1, decode p2, decode p3)
    | field, `List [specname;`List args] when String.equal "ASpecApply" field ->
      SpecApply (to_string specname, List.map E.SE.decode args)
    | _ -> raise e

  let spec_tpname = "spec"

  let spec_encode (args, specbody) =
    `Assoc ["treetp", `String spec_tpname;
            "args", `List (List.map T.tpedvar_encode args);
            "specbody", E.forallformula_encode specbody]

  let spec_decode json =
    let e = InterExn (Printf.sprintf "%s::decode wrong type" spec_tpname) in
    let open Util in
    let treetp = json |> member "treetp" |> to_string in
    if String.equal spec_tpname treetp then
      let qv =
        match json |> member "args" with
        | `List qv -> List.map T.tpedvar_decode qv
        | _ -> raise e
      in
      let body = json |> member "specbody" |> E.forallformula_decode in
      (qv, body)
    else raise e

  let spectable_encode tab =
    let j = StrMap.fold (fun name spec r ->
        (* let _ = printf "spectable_encode find name:%s\n" name in *)
        (`Assoc ["name", `String name;
                 "spec", spec_encode spec]) :: r
      ) tab [] in
    `List j

  let spectable_decode = function
    | `List l ->
      List.fold_left (fun r json ->
          let name = json |> Util.member "name" |> Util.to_string in
          (* let _ = printf "spectable_decode find name:%s\n" name in *)
          let spec = json |> Util.member "spec" |> spec_decode in
          StrMap.add name spec r
        ) StrMap.empty l
    | _ -> raise @@ InterExn (Printf.sprintf "%s::decode wrong type" "spec table")

  let spec_eq (args1, body1) (args2, body2) =
    if List.length args1 != List.length args2
    then false
    else
    (List.for_all (fun (arg1, arg2) ->
        T.tpedvar_eq arg1 arg2
        ) (List.combine args1 args2)) && (E.eq_forallformula body1 body2)

  let spectable_eq_succ t1 t2 =
    StrMap.fold (fun name spec r ->
        if not r then false else
          match StrMap.find_opt t2 name with
          | Some spec' when spec_eq spec spec' -> true
          | Some spec' ->
            (printf "%s not eq!\nspec 1:\n%s\nspec 2:\n%s\n"
               name (layout_spec spec) (layout_spec spec');
             false)
          | _ ->
            (printf "%s not eq!\nspec 1:\n%s\nspec 2:\n%s\n"
               name (layout_spec spec) "none";
             false)
      ) t1 true

  let spectable_eq t1 t2 =
    (spectable_eq_succ t1 t2) (* && (spectable_eq_succ t2 t1) *)
end
