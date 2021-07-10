let preds = [|"mem"; "left"|]
let pre (x: int) (tree1: Unbset.t) (tree2: Unbset.t) =
  fun (u: int) (v: int) ->
  implies (left tree1 u v) (v > u)
let post (x: int) (tree1: Unbset.t) (tree2: Unbset.t) =
  fun (u: int) (v: int) ->
  (implies (left tree2 u v) (v > u)) && (iff (mem tree2 u) (mem tree1 u || u == x))
