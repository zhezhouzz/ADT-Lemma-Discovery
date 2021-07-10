let preds = [|"mem"|]
let post (tree1: Leftisthp.t) (tree2: Leftisthp.t) (tree3: Leftisthp.t) =
  fun (u: int) ->
  (iff (mem tree3 u) (mem tree1 u || mem tree2 u))
