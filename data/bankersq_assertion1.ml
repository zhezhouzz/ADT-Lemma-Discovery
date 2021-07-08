let preds = [|"mem"|]
let post
    (lenf: int) (f: Bankersq.t) (lenr: int) (r: Bankersq.t) (x: int)
    (lenf': int) (f': Bankersq.t) (lenr': int) (r': Bankersq.t) =
  fun (u: int) ->
  (iff (mem f u || mem r u || u == x) (mem f' u || mem r' u))
