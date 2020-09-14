module type Value = sig
  type t =
    | L of int list
    | T of int Utils.Tree.t
    | I of int
    | B of bool
    | NotADt
  val layout : t -> string
  val eq : t -> t -> bool
  val flatten_forall: t -> int list
end

module Value: Value = struct
  open Utils
  open Printf
  type t =
    | L of int list
    | T of int Utils.Tree.t
    | I of int
    | B of bool
    | NotADt
  let layout = function
    | L l -> sprintf "[%s]" (IntList.to_string l)
    | T tr -> Tree.layout string_of_int tr
    | I i -> string_of_int i
    | B b -> string_of_bool b
    | NotADt -> "_"
  let eq x y =
    let aux = function
      | (I x, I y) -> x == y
      | (B x, B y) -> x == y
      | (L x, L y) -> List.eq (fun x y -> x == y) x y
      | (T x, T y) -> Tree.eq (fun x y -> x == y) x y
      | (_, _) -> false
    in
    aux (x, y)
  let flatten_forall = function
    | I _ | B _ | NotADt -> raise @@ InterExn "flatten_forall: not a datatype"
    | L il -> List.flatten_forall (fun x y -> x == y) il
    | T it -> Tree.flatten_forall (fun x y -> x == y) it
end
