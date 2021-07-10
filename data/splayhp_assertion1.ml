let preds = [|"mem"|]
let post (x: int) (tree1: Splayhp.t) (tree2: Splayhp.t) (tree3: Splayhp.t) =
  fun (u: int) ->
  (iff (mem tree1 u) (mem tree2 u || mem tree3 u))
