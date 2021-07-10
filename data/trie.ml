module type Trie = sig
  type t
  type tp
  val nil: tp
  val cons: int -> tp -> tp
  val node: t -> int -> t -> t
  val leaf: t
end

val ins: int -> Trie.tp -> int -> Trie.t -> Trie.t

let rec ins (default: int) (i: Trie.tp) (a: int) (m: Trie.t) =
  match m with
  | _ when Trie.leaf ->
    (match i with
     | _ when Trie.nil -> (Trie.node m a m)
     | _ when Trie.cons (z1: int) (i1: Trie.tp) ->
       if z1 > 0
       then Trie.node (ins default i1 a m) default m
       else Trie.node m default (ins default i1 a m)
    )
  | _ when (Trie.node (l: Trie.t) (y: int) (r: Trie.t))->
    (match i with
     | _ when (Trie.nil) -> Trie.node l a r
     | _ when (Trie.cons (z2: int) (i2: Trie.tp)) ->
       if z2 > 0
       then Trie.node (ins default i2 a l) y r
       else Trie.node l y (ins default i2 a r)
    )
