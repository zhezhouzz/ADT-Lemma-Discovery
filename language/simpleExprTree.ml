module type SimpleExprTree = sig
  module L: Lit.Lit
  type tp = Tp.Tp.t
  type op = string

  type t =
    | Literal of tp * L.t
    | Var of tp * string
    | Op of tp * op * t list

  val layout: t -> string
  val subst: t -> string list -> t list -> t
  val eq: t -> t -> bool
  val var_to_tp_name: t -> (int list * (tp * string) list)
  val get_tp: t -> tp
  val to_tpedvar: t -> Tp.Tp.tpedvar
  val from_tpedvar: Tp.Tp.tpedvar -> t
  val encode: t -> Yojson.Basic.t
  val decode: Yojson.Basic.t -> t
end

module SimpleExprTree (L: Lit.Lit) : SimpleExprTree
  with type L.t = L.t = struct
  module L = L
  module T = Tp.Tp
  type tp = Tp.Tp.t
  type op = string

  type t =
    | Literal of tp * L.t
    | Var of tp * string
    | Op of tp * op * t list
  open Utils
  let get_tp = function
    | Literal (tp, _) -> tp
    | Var (tp, _) -> tp
    | Op (tp, _, _) -> tp

  let layout_op op args =
    match op, args with
    | "+", [a; b] -> Printf.sprintf "(%s+%s)" a b
    | "-", [a; b] -> Printf.sprintf "%s-%s" a b
    | "==", [a; b] -> Printf.sprintf "(%s==%s)" a b
    | "<>", [a; b] -> Printf.sprintf "(%s<>%s)" a b
    | ">=", [a; b] -> Printf.sprintf "(%s>=%s)" a b
    | "<=", [a; b] -> Printf.sprintf "(%s<=%s)" a b
    | ">", [a; b] -> Printf.sprintf "(%s>%s)" a b
    | "<", [a; b] -> Printf.sprintf "(%s<%s)" a b
    | pred, args -> Printf.sprintf "%s(%s)" pred (List.to_string (fun x -> x) args)

  let rec layout = function
    | Literal (_, x) -> L.layout x
    | Var (_, name) -> name
    | Op (_, op, args) -> layout_op op (List.map layout args)


  let subst expr args argsvalue =
    let l = List.combine args argsvalue in
    let rec aux expr =
      match expr with
      | Literal _ -> expr
      | Var (_, name) ->
        (match List.find_opt (fun (name', _) -> String.equal name name') l with
         | None -> expr
         | Some (_, b) -> b
        )
      | Op (tp, op, args) -> Op (tp, op, List.map aux args)
    in
    aux expr

  let eq a b =
    let rec aux = function
      | Literal (tp1, x1), Literal (tp2, x2) -> (T.eq tp1 tp2) && (L.eq x1 x2)
      | Var (tp1, name1), Var (tp2, name2) -> (T.eq tp1 tp2) && (String.equal name1 name2)
      | Op (tp1, op1, args1), Op (tp2, op2, args2) ->
        (T.eq tp1 tp2) && (String.equal op1 op2) &&
        (List.for_all2 (fun a b -> aux (a, b)) args1 args2)
      | _ -> false
    in
    aux (a, b)

  let rec var_to_tp_name = function
    | Var (tp, name) -> [], [tp, name]
    | Literal (Int, L.Int i) -> [i], []
    | Literal (_, _) -> [], []
    | Op (_, _, args) ->
      let a, b = List.split (List.map var_to_tp_name args) in
      List.flatten a, List.flatten b

  let to_tpedvar = function
    | Var (tp, name) -> (tp, name)
    | _ -> raise @@ InterExn "SE::to_tpedvar"

  let from_tpedvar (tp, name) = Var (tp, name)

  open Yojson.Basic
  let treetp_name = "S"
  let encode_field = encode_field_ treetp_name
  let decode_field = decode_field_ treetp_name
  let rec encode = function
    | Literal (tp, lit) -> encode_field "Lit" (`List [T.encode tp; L.encode lit])
    | Var (tp, name) -> encode_field "V" (`List [T.encode tp; `String name])
    | Op (tp, op, args) ->
      encode_field "Op" (`List [T.encode tp; `String op; `List (List.map encode args)])
  let rec decode json =
    let e = InterExn (Printf.sprintf "%s::decode wrong field" treetp_name) in
    let open Util in
    let field, value = decode_field json in
    match field, value with
    | field, `List [tp; lit] when String.equal "Lit" field ->
      Literal (T.decode tp, L.decode lit)
    | field, `List [tp; name] when String.equal "V" field ->
      Var (T.decode tp, to_string name)
    | field, `List [tp; op; `List args] when String.equal "Op" field ->
      Op (T.decode tp, to_string op, List.map decode args)
    | _ -> raise e
end
