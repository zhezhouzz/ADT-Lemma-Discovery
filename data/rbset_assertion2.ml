let preds = [|"mem"; "left"; "right"; "para"|]
let prerr_newline (r: bool) (tree1: Rbset.t) (x: int) (tree2: Rbset.t) (tree3: Rbset.t) =
  fun (u: int) (v: int) ->
  (implies (left tree1 u v || right tree1 u v || para tree1 u v) (u != v)) &&
  (implies (left tree2 u v || right tree2 u v || para tree2 u v) (u != v)) &&
  (implies (mem tree1 u && mem tree2 v) (u != v)) &&
  (implies (mem tree1 u || mem tree2 u) (u != x))
let post (r: bool) (tree1: Rbset.t) (x: int) (tree2: Rbset.t) (tree3: Rbset.t) =
  fun (u: int) (v: int) ->
  (implies (left tree3 u v || right tree3 u v || para tree3 u v) (u != v)) &&
  (iff (mem tree3 u) (mem tree1 u || mem tree2 u || u == x))
