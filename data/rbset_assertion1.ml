let preds = [|"mem"|]
let post (r: bool) (tree1: Rbset.t) (x: int) (tree2: Rbset.t) (tree3: Rbset.t) =
  fun (u: int) ->
  (iff (mem tree3 u) (mem tree1 u || mem tree2 u || u == x))
