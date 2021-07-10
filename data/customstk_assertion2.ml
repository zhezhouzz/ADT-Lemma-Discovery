let preds = [|"mem"; "ord"|]
let pre (l1: Customstk.t) (l2: Customstk.t) (l3: Customstk.t) = true
let post (l1: Customstk.t) (l2: Customstk.t) (l3: Customstk.t) =
  fun (u: int) ->
    (implies (mem l3 u) (mem l1 u && mem l2 u))
