let rec member l u =
  match l with
  | [] -> false
  | h :: t -> if u == h then true else member t u

let rec order l u v =
  match l with
  | [] -> false
  | [_] -> false
  | h1 :: h2 :: t ->
    if h1 == u
    then (if h2 == v then true else order (h1 :: t) u v)
    else order (h2::t) u v

let head l u =
  match l with
  | [] -> false
  | h :: _ -> h == u
