let preds = [|"mem"; "ance"|]
let post (x: int) (tree1: Unbset.t) (tree2: Unbset.t) =
  fun (u: int) ->
  (iff (mem tree2 u) (mem tree1 u && u == x))
