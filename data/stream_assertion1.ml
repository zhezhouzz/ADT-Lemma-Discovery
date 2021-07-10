let preds = [|"mem"|]
let post (acc: Stream.t) (s: Stream.t) (nu: Stream.t) =
  fun (u: int) ->
  (implies (mem nu u) (mem acc u || mem s u))
