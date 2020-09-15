exception TestFailedException of string
exception InterExn of string

module StrMap = Map.Make(String);;
module IntMap = Map.Make(struct type t = int let compare = compare end);;

module List = struct
  include List
  let eq compare l1 l2 =
    let rec aux = function
      | ([], []) -> true
      | (h1 :: t1, h2 :: t2) -> if compare h1 h2 then aux (t1, t2) else false
      | (_, _) -> false
    in
    aux (l1, l2)

  let order eq l u v =
    let rec aux = function
      | [] -> false
      | h::t ->
        if eq u h
        then List.exists (fun x -> eq x v) t
        else aux t
    in
    aux l
  let for_alli f l =
    let rec aux i = function
      | [] -> true
      | h :: t ->
        if (f h i) then aux (i+1) t else false
    in
    aux 0 l

  let fold_lefti f default l =
    let rec aux r i = function
      | [] -> r
      | h :: t -> aux (f r i h) (i + 1) t
    in
    aux default 0 l

  let first l =
    match l with
    | [] -> raise @@ InterExn "list_first"
    | h :: _ -> h

  let last l =
    let l = List.rev l in
    match l with
    | [] -> raise @@ InterExn "list_last"
    | h :: _ -> h

  let to_string f l =
    fold_lefti (fun res i a -> if i == 0 then res ^ (f a) else res ^ "," ^ (f a)) "" l

  let rec check_list_unique eq l =
    let rec aux e = function
      | [] -> true
      | h :: t -> if eq e h then false else aux e t
    in
    match l with
    | [] -> true
    | h :: t -> if aux h t then check_list_unique eq t else false

  let remove_elt compare e l =
    let rec go l acc = match l with
      | [] -> List.rev acc
      | x::xs when compare e x -> go xs acc
      | x::xs -> go xs (x::acc)
    in go l []

  let remove_duplicates compare l =
    let rec go l acc = match l with
      | [] -> List.rev acc
      | x :: xs -> go (remove_elt compare x xs) (x::acc)
    in go l []

  let inner_layout l split default =
    match l with
    | [] -> default
    | h :: t -> List.fold_left (fun res x -> res ^ split ^ x) h t
  let flatten_forall = remove_duplicates

  let combination num_all num_choose =
    let rec aux prefix rest_num rest_elems =
      if rest_num > (List.length rest_elems) then []
      else if rest_num == 0 then [prefix]
      else if rest_num == 1 then List.fold_left (fun r x -> (x::prefix) :: r) [] rest_elems else
        match rest_elems with
        | [] -> []
        | h :: t ->
          (aux (h::prefix) (rest_num - 1) t) @ (aux prefix rest_num t)
    in
    let elems = List.init num_all (fun x -> x) in
    aux [] num_choose elems

  let combination_l l num_choose =
    let c = combination (List.length l) num_choose in
    List.map (fun ids -> List.map (fun id -> List.nth l id) ids) c

  let combination_l_all l =
    let len = List.length l in
    let rec aux num_choose result =
      if num_choose > len then result else
        aux (num_choose + 1) (result @ (combination_l l num_choose))
    in
    aux 0 []

  let permutation l =
    let insert_all_positions x l =
      let rec aux prev acc l =
        match l with
        | [] -> (prev @ [x]) :: acc |> List.rev
        | hd::tl as l -> aux (prev @ [hd]) ((prev @ [x] @ l) :: acc) tl
      in aux [] [] l
    in
    let rec aux = function
      | [] -> []
      | hd::[] -> [[hd]]
      | hd::tl -> List.fold_left (fun acc p -> acc @ insert_all_positions hd p) [] (aux tl)
    in
    aux l

  let cross l0 l1 =
    if ((List.length l0) == 0) || ((List.length l1) == 0) then []
    else
      let rec aux i j res =
        if j >= (List.length l1) then aux (i + 1) 0 res
        else if i >= (List.length l0) then res
        else aux i (j+1) ((List.nth l0 i, List.nth l1 j) :: res)
      in
      aux 0 0 []

  let match_snoc l =
    let l = List.rev l in
    match l with
    | [] -> raise @@ InterExn "match_snoc: []"
    | h :: t -> List.rev t, h

  let union compare l0 l1 = remove_duplicates compare (l0 @ l1)

  let shape_reverse ll =
    let nth l id =
      try (List.nth l id) with
      | Failure _ -> raise @@ InterExn "shape_reverse"
      | Invalid_argument _ -> raise @@ InterExn "shape_reverse"
    in
    List.init (List.length ll) (fun i -> List.map (fun l -> nth l i) ll)
end

module Tree = struct
  type 'a t =
    | Leaf
    | Node of ('a * 'a t * 'a t)

  let exists f t =
    let rec aux before t =
      if before then true else
        match t with
        | Leaf -> false
        | Node (e, l, r) ->
          if f e then true else
            aux (aux before l) r
    in
    aux false t
  let layout _ _ = "tree"

  let left_child eq t u v =
    let rec aux before t =
      if before then true else
        match t with
        | Leaf -> false
        | Node (a, l, r) ->
          if eq a u
          then exists (fun x -> eq x v) l
          else aux (aux before l) r
    in
    aux false t

  let right_child eq t u v =
    let rec aux before t =
      if before then true else
        match t with
        | Leaf -> false
        | Node (a, l, r) ->
          if eq a u
          then exists (fun x -> eq x v) r
          else aux (aux before l) r
    in
    aux false t

  let parallel_child eq t u v =
    let rec aux = function
      | Leaf -> false
      | Node (_, l, r) ->
        ((exists (fun x -> eq x u) l) && (exists (fun x -> eq x v) r)) || (aux l) || (aux r)
    in
    aux t

  let eq compare t1 t2 =
    let rec aux = function
      | (Leaf, Leaf) -> true
      | (Node (a1, l1, r1), Node (a2, l2, r2)) ->
        if compare a1 a2 then
          if aux (l1, l2)
          then aux (r1, r2)
          else false
        else false
      | (_, _) -> false
    in
    aux (t1, t2)

  let rec flatten = function
    | Leaf -> []
    | Node (a, l, r) -> a::((flatten l) @ (flatten r))
  let flatten_forall compare t =
    List.remove_duplicates compare (flatten t)
  let union l0 l1 = List.union (fun x y -> x == y) l0 l1
end

module IntList = struct
  let exists x l = List.exists (fun a -> a == x) l
  let contain l0 l1 = List.for_all (fun x -> exists x l1) l0
  let rec keep_ord l0 l1 =
    let rec aux a b = function
      | [] -> false
      | h :: t -> if h == a then exists b t else aux a b t
    in
    let rec aux2 a = function
      | [] -> true
      | h :: t -> (aux a h l1) && aux2 a t
    in
    match l0 with
    | [] -> true
    | h :: t -> (aux2 h t) && keep_ord t l1
  let forall_ge l = List.for_alli (fun h i -> h >= i) l
  let forall_gt l = List.for_alli (fun h i -> h > i) l
  let forall_eq l = List.for_alli (fun h i -> h == i) l
  let eq l0 l1 = List.eq (fun x y -> x == y) l0 l1
  let to_string l =
    List.fold_lefti (fun res i a ->
        if i == 0 then res ^ (string_of_int a) else res ^ ";" ^ (string_of_int a)) "" l
  let max_opt l =
    let rec aux m = function
      | [] -> m
      | h :: t -> if h > m then aux h t else aux m t
    in
    match l with
    | [] -> None
    | h :: t -> Some (aux h t)
end

let list_list_foldl l0 l1 default0 default1 f0 f1 =
  List.fold_left (fun res0 a ->
      f0 res0 (List.fold_left (fun res1 b -> f1 res1 a b) default1 l1)
    ) default0 l0

let ll_in_range_first f l0 l1 =
  ((List.length l0) <= (List.length l1)) &&
  List.fold_lefti (fun r i a -> r && (f a (List.nth l1 i))) true l0

let boollist_to_string l =
  List.fold_lefti (fun res i a ->
      if i == 0 then res ^ (string_of_bool a) else res ^ ";" ^ (string_of_bool a)) "" l

let sublist l s e =
  let rec aux i result = function
    | [] -> result
    | h :: t ->
      if (i >= s) && (i < e)
      then aux (i+1) (result @ [h]) t
      else if i < s
      then aux (i+1) result t
      else result
  in
  aux 0 [] l

let map_double f (a, b) = (f a, f b)
let map_triple f (a, b, c) = (f a, f b, f c)
let map4 f (a, b, c, d) = (f a, f b, f c, f d)
let map5 f (a, b, c, d, e) = (f a, f b, f c, f d, f e)
