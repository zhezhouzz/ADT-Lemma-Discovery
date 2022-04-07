module type Value = sig
  type t =
    | L of int list
    | T of int Utils.Tree.t
    | I of int
    | B of bool
    | TI of (int, int) Utils.LabeledTree.t
    | TB of (int, bool) Utils.LabeledTree.t
    | NotADt
  [@@deriving sexp]
  type ts = t list [@@deriving sexp]
  type tss = t list list [@@deriving sexp]
  type nss = (string * t list list) list [@@deriving sexp]
  val layout : t -> string
  val eq : t -> t -> bool
  val flatten_forall: t -> int list
  val flatten_forall_l: t list -> int list
  val get_tp: t -> Tp.Tp.t
end

module Value: Value = struct
  open Utils
  open Printf
  open Sexplib.Std
  type t =
    | L of int list
    | T of int Utils.Tree.t
    | I of int
    | B of bool
    | TI of (int, int) Utils.LabeledTree.t
    | TB of (int, bool) Utils.LabeledTree.t
    | NotADt
  [@@deriving sexp]
  type ts = t list [@@deriving sexp]
  type tss = t list list [@@deriving sexp]
  type nss = (string * t list list) list [@@deriving sexp]
  let layout = function
    | L l -> sprintf "[%s]" (IntList.to_string l)
    | T tr -> Tree.layout string_of_int tr
    | I i -> string_of_int i
    | B b -> string_of_bool b
    | TI tr -> LabeledTree.layout string_of_int tr
    | TB tr -> LabeledTree.layout string_of_int tr
    | NotADt -> "_"
  let eq x y =
    let aux = function
      | (I x, I y) -> x == y
      | (B x, B y) -> x == y
      | (L x, L y) -> List.eq (fun x y -> x == y) x y
      | (T x, T y) -> Tree.eq (fun x y -> x == y) x y
      | (TI x, TI y) -> LabeledTree.eq (fun x y -> x == y) (fun x y -> x == y) x y
      | (TB x, TB y) -> LabeledTree.eq (fun x y -> x == y) (fun x y -> x == y) x y
      | (_, _) -> false
    in
    aux (x, y)
  let flatten_forall = function
    | I _ | B _ | NotADt -> raise @@ InterExn "flatten_forall: not a datatype"
    | L il -> List.flatten_forall (fun x y -> x == y) il
    | T it -> Tree.flatten_forall (fun x y -> x == y) it
    | TI iti -> LabeledTree.flatten_forall (fun x y -> x == y) iti
    | TB itb -> LabeledTree.flatten_forall (fun x y -> x == y) itb
  let flatten_forall_l l =
    List.fold_left (fun r v ->
        match v with
        | I i -> i :: r
        | B _ -> r
        | L il -> (List.flatten_forall (fun x y -> x == y) il) @ r
        | T it -> (Tree.flatten_forall (fun x y -> x == y) it) @ r
        | TI iti -> (LabeledTree.flatten_forall (fun x y -> x == y) iti) @ r
        | TB itb -> (LabeledTree.flatten_forall (fun x y -> x == y) itb) @ r
        | NotADt -> raise @@ InterExn "flatten_forall_l: not a value"
      ) [] l
  module T = Tp.Tp
  let get_tp v =
    match v with
    | I _ -> T.Int
    | B _ -> T.Bool
    | L _ -> T.IntList
    | T _ -> T.IntTree
    | TI _ -> T.IntTreeI
    | TB _ -> T.IntTreeB
    | NotADt -> raise @@ InterExn "get_tp: not a value"
end
