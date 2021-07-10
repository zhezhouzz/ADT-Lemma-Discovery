let preds = [|"mem"; "ord"|]
let post (acc: Stream.t) (s: Stream.t) (nu: Stream.t) =
  fun (u: int) (v: int) ->
  (implies (ord acc u v || ord s v u || (mem s u && mem acc v)) (ord nu u v)) &&
  (iff (mem nu u) (mem acc u || mem s u))
