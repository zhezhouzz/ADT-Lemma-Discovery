let preds = [|"mem"; "ance"|]
let pre (tree1: Leftisthp.t) (tree2: Leftisthp.t) (tree3: Leftisthp.t) =
  fun (u: int) (v: int) ->
  (implies (ance tree1 u v) (u <= v)) && (implies (ance tree2 u v) (u <= v))
let post (tree1: Leftisthp.t) (tree2: Leftisthp.t) (tree3: Leftisthp.t) =
  fun (u: int) (v: int) ->
  (implies (ance tree3 u v) (u <= v)) &&
  (iff (mem tree3 u) (mem tree1 u || mem tree2 u))
