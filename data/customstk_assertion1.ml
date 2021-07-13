let preds = [|"hd"; "mem"|]
let post (l1: Customstk.t) (l2: Customstk.t) (l3: Customstk.t) =
  fun (u: int) ->
    (iff (mem l3 u) (mem l1 u || mem l2 u)) &&
    (implies (hd l3 u) (hd l1 u || hd l2 u))
