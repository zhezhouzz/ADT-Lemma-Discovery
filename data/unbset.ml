module type Unbset = sig
  type t
  val leaf: t
  val node: t -> int -> t -> t
end

val insert: int -> Unbset.t -> Unbset.t

let rec insert (x: int) (tree3: Unbset.t) =
  match tree3 with
  | _ when Unbset.leaf -> Unbset.node tree3 x tree3
  | _ when Unbset.node (tree1: Unbset.t) (y: int) (tree2: Unbset.t) ->
    if x < y then Unbset.node (insert y tree1) x tree2
    else if y < x then Unbset.node tree1 y (insert x tree2)
    else Unbset.node tree1 y tree2
