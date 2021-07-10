let preds = [|"mem"; "ord"|]
let post
    (lenf: int) (f: Bankersq.t) (lenr: int) (r: Bankersq.t) (x: int)
    (lenf': int) (f': Bankersq.t) (lenr': int) (r': Bankersq.t) =
  fun (u: int) ->
  (iff (mem f u || mem r u) ((mem f' u && mem r' x) || ord r' x u || ord f' u x))
