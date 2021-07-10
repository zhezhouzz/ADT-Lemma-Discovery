let preds = [|"once"; "mem"; "ord"|]
let post (acc: Stream.t) (s: Stream.t) (nu: Stream.t) =
  fun (u: int) (v: int) ->
  (implies
     (once acc u && once s v && ord acc u v && (not (mem s u)) && (not (mem acc v)))
     (ord nu u v && (not (ord nu v u)))) &&
  (iff (mem nu u) (mem acc u || mem s u))
