let preds = [|"hd"; "mem"; "ord"|]

let pre (l1: Customstk.t) (l2: Customstk.t) (l3: Customstk.t) = true

let post (l1: Customstk.t) (l2: Customstk.t) (l3: Customstk.t) =
  fun (u: int) (v: int) ->
    (implies (ord l1 u v || ord l2 u v) (ord l3 u v))