let preds = [|"mem"; "hd"; "ord"|]
let pre (l1: Customstk.t) (l2: Customstk.t) (l3: Customstk.t) = true
let post (l1: Customstk.t) (l2: Customstk.t) (l3: Customstk.t) =
  fun (u: int) (v: int) ->
    (iff (mem l3 u) (mem l1 u || mem l2 u)) &&
    (implies (ord l1 u v || ord l2 u v) (ord l3 u v))
