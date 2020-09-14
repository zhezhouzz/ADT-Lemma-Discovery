module type SimpleExprTree = sig
  module L: Lit.Lit
  type tp =
    | Bool
    | Int
    | IntList
    | IntTree
  type op = string

  type t =
    | Literal of tp * L.t
    | Var of tp * string
    | Op of tp * op * t list

  val eq_tp: tp * tp -> bool
  val layout_tp: tp -> string
  val layout: t -> string
  val subst: t -> string list -> t list -> t
end

module SimpleExprTree (L: Lit.Lit) : SimpleExprTree
  with type L.t = L.t = struct
  module L = L
  type tp =
    | Bool
    | Int
    | IntList
    | IntTree
  type op = string

  type t =
    | Literal of tp * L.t
    | Var of tp * string
    | Op of tp * op * t list
  open Utils
  let layout_tp = function
    | Bool -> "bool"
    | Int -> "int"
    | IntList -> "int list"
    | IntTree -> "int tree"

  let eq_tp = function
    | (Int, Int) -> true
    | (Bool, Bool) -> true
    | (IntList, IntList) -> true
    | (IntTree, IntTree) -> true
    | _ -> false

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
end
