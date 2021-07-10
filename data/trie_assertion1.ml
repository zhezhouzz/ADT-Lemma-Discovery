let preds = [|"mem"|]
let post (default: int) (i: Trie.tp) (a: int) (m: Trie.t) (nu: Trie.t) =
  fun (u: int) ->
  (implies (mem nu u) (mem m u || u == default || u == a))
