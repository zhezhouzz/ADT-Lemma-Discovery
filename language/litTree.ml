module type LitTree = sig
  type t =
    | Int of int
    | Bool of bool
    | IntList of int list
    | IntTree of int Utils.Tree.t
  val layout : t -> string
  val eq : t -> t -> bool
  val encode: t -> Yojson.Basic.t
  val decode: Yojson.Basic.t -> t
end

module LitTree : LitTree = struct
  type t =
    | Int of int
    | Bool of bool
    | IntList of int list
    | IntTree of int Utils.Tree.t
  open Utils
  let layout = function
    | Int x -> string_of_int x
    | Bool b -> string_of_bool b
    | IntList l -> IntList.to_string l
    | IntTree t -> Tree.layout string_of_int t
  let eq x y =
    let aux = function
      | (Int x, Int y) -> x == y
      | (Bool x, Bool y) -> x == y
      | (IntList x, IntList y) -> List.eq (fun x y -> x == y) x y
      | (IntTree x, IntTree y) -> Tree.eq (fun x y -> x == y) x y
      | (_, _) -> false
    in
    aux (x, y)

  open Yojson.Basic
  let treetp_name = "Lit"
  let encode_field = encode_field_ treetp_name
  let decode_field = decode_field_ treetp_name
  let encode = function
    | Int i -> encode_field "Int" (`Int i)
    | Bool b -> encode_field "Bool" (`Bool b)
    | _ -> raise @@ InterExn "Lit::encode"
  let decode json =
    let e = InterExn (Printf.sprintf "%s::decode wrong field" treetp_name) in
    let open Util in
    let field, value = decode_field json in
    if String.equal "Int" field
    then Int (to_int value)
    else if String.equal "Bool" field
    then Bool (to_bool value)
    else raise e
end
