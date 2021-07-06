let pre (l1: Stack.t) (l2: Stack.t) (l3: Stack.t) = true
let post (l1: Stack.t) (l2: Stack.t) (l3: Stack.t) =
  fun (u: int) ->
    (iff (mem l3 u) (mem l1 u || mem l2 u)) &&
    (implies (hd l3 u) (hd l1 u || hd l2 u))
