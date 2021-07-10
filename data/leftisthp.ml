module type Leftisthp = sig
  type t
  val leaf: t
  val make_tree: int -> t -> t -> t
  val tree: int -> int -> t -> t -> t
end

val merge: Leftisthp.t -> Leftisthp.t -> Leftisthp.t

let rec merge (tree1: Leftisthp.t) (tree2: Leftisthp.t) =
  match tree1, tree2 with
  | _ when ((tree11: Leftisthp.t), Leftisthp.leaf) -> tree11
  | _ when (Leftisthp.leaf, (tree22: Leftisthp.t)) -> tree22
  | _ when (Leftisthp.tree (rank1: int) (x: int) (a1: Leftisthp.t) (b1: Leftisthp.t),
               Leftisthp.tree (rank2: int) (y: int) (a2: Leftisthp.t) (b2: Leftisthp.t)) ->
    if x <= y then Leftisthp.make_tree x a1 (merge b1 tree2)
    else Leftisthp.make_tree y a2 (merge tree1 b2)
