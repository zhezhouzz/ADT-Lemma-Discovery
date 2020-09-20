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

  val eq_tp: tp -> tp -> bool
  val layout_tp: tp -> string
  val layout: t -> string
  val subst: t -> string list -> t list -> t
  val eq: t -> t -> bool
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

  let eq_tp_ = function
    | (Int, Int) -> true
    | (Bool, Bool) -> true
    | (IntList, IntList) -> true
    | (IntTree, IntTree) -> true
    | _ -> false
  let eq_tp a b = eq_tp_ (a, b)

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
    | Literal (tp1, x1), Literal (tp2, x2) -> (eq_tp tp1 tp2) && (L.eq x1 x2)
    | Var (tp1, name1), Var (tp2, name2) -> (eq_tp tp1 tp2) && (String.equal name1 name2)
    | Op (tp1, op1, args1), Op (tp2, op2, args2) ->
      (eq_tp tp1 tp2) && (String.equal op1 op2) &&
      (List.for_all2 (fun a b -> aux (a, b)) args1 args2)
    | _ -> false
  in
  aux (a, b)
end
