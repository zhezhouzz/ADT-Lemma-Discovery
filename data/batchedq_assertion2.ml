let preds = [|"mem"; "hd"; "ord"|]
let post (f: Batchedq.t) (r: Batchedq.t) (f': Batchedq.t) (r': Batchedq.t) =
  fun (u: int) (v: int) ->
  (iff (mem f' u || mem r' u || hd f u) (mem f u || mem r u)) &&
  (implies (ord f' u v || ord r' v u) (ord f u v || ord r v u))
