module type Rbset = sig
  type t
  val tree: bool -> t -> int -> t -> t
end

val balance: bool -> Rbset.t -> int -> Rbset.t -> Rbset.t

let rec balance (r: bool) (tree1: Rbset.t) (x: int) (tree2: Rbset.t) =
  match r, tree1, x, tree2 with
  | _ when (false,
            Rbset.tree true (Rbset.tree true (a1: Rbset.t) (x1: int) (b1: Rbset.t)) (y1: int) (c1: Rbset.t),
            (z1: int),
            (d1: Rbset.t)) ->
    Rbset.tree true (Rbset.tree false a1 x1 b1) y1 (Rbset.tree false c1 z1 d1)
  | _ when (false,
            Rbset.tree true (a2: Rbset.t) (x2: int) (Rbset.tree true (b2: Rbset.t) (y2: int) (c2: Rbset.t)),
            (z2: int),
            (d2: Rbset.t)) ->
    Rbset.tree true (Rbset.tree false a2 x2 b2) y2 (Rbset.tree false c2 z2 d2)
  | _ when (false,
            (a3: Rbset.t),
            (x3: int),
            Rbset.tree true (Rbset.tree true (b3: Rbset.t) (y3: int) (c3: Rbset.t)) (z3: int) (d3: Rbset.t)) ->
    Rbset.tree true (Rbset.tree false a3 x3 b3) y3 (Rbset.tree false c3 z3 d3)
  | _ when (false,
            (a4: Rbset.t),
            (x4: int),
            Rbset.tree true (b4: Rbset.t) (y4: int) (Rbset.tree true (c4: Rbset.t) (z4: int) (d4: Rbset.t))) ->
    Rbset.tree true (Rbset.tree false a4 x4 b4) y4 (Rbset.tree false c4 z4 d4)
  | _ when ((r5: bool), (tree15: Rbset.t), (x5: int), (tree25: Rbset.t)) ->
    Rbset.tree r5 tree15 x5 tree25
