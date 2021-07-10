let preds = [|"mem"; "left"; "right"|]
let pre (x: int) (tr1: Splayhp.t) (tr2: Splayhp.t) (tr3: Splayhp.t) =
  fun (u: int) (v: int) ->
  (implies (left tr1 u v) (u >= v)) && (implies (right tr1 u v) (u <= v))
let post (x: int) (tr1: Splayhp.t) (tr2: Splayhp.t) (tr3: Splayhp.t) =
  fun (u: int) ->
  (implies (mem tr2 u) (u <= x)) && (implies (mem tr3 u) (u >= x)) && (iff (mem tr1 u) (mem tr2 u || mem tr3 u))
