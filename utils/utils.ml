exception TestFailedException of string
exception InterExn of string
exception UndefExn of string

let addadd x = (x := !x + 1)

let make_dir name =
  Core.Unix.mkdir_p name

(* module StrMap = Map.Make(String);; *)
module IntMap = Map.Make(struct type t = int let compare = compare end);;

module StrMap = struct
  include Map.Make(String)
  let find info m k =
    match find_opt k m with
    | None -> raise @@ InterExn info
    | Some v -> v
  let find_opt m k = find_opt k m
  let to_value_list m = fold (fun _ v l -> v :: l) m []
  let to_key_list m = fold (fun k _ l -> k :: l) m []
  let to_kv_list m = fold (fun k v l -> (k,v) :: l) m []
  let from_kv_list l =
    List.fold_left (fun m (k, v) ->
        add k v m
      ) empty l
end

module Renaming = struct
  let universe_label = ref 0
  let name () =
    let n =  Printf.sprintf "x!!%i" (!universe_label) in
    universe_label := (!universe_label) + 1; n
  let name_tab = Hashtbl.create 100
  open Printf
  let unique name =
    match Hashtbl.find_opt name_tab name with
    | Some n -> Hashtbl.replace name_tab name (n+1); sprintf "%s%i" name (n+1)
    | None -> Hashtbl.add name_tab name 0; sprintf "%s%i" name 0
end

module List = struct
  include List

  let is_empty = function
    | [] -> true
    | _ -> false

  let eq compare l1 l2 =
    let rec aux = function
      | ([], []) -> true
      | (h1 :: t1, h2 :: t2) -> if compare h1 h2 then aux (t1, t2) else false
      | (_, _) -> false
    in
    aux (l1, l2)

  let find info f l =
    match find_opt f l with
    | None -> raise @@ InterExn info
    | Some v -> v

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

  let find_index_opt f l =
    fold_lefti (fun r i x ->
        match r with
        | Some _ -> r
        | None -> if f x then Some i else None
      ) None l

  let find_index info f l =
    match find_index_opt f l with
    | None -> raise @@ InterExn ("List:: " ^ info)
    | Some i -> i

  let first l =
    match l with
    | [] -> raise @@ InterExn "list_first"
    | h :: _ -> h

  let last l =
    let l = List.rev l in
    match l with
    | [] -> raise @@ InterExn "list_last"
    | h :: _ -> h

  let lastb l e =
    let l = List.rev l in
    match l with
    | [] -> false
    | h :: _ -> h == e

  let to_string f l =
    fold_lefti (fun res i a -> if i == 0 then res ^ (f a) else res ^ "," ^ (f a)) "" l

  let rec element_unique f l e =
    match l with
    | [] -> None
    | h :: t -> if f e h then Some t else element_unique f t e

  let once f l e =
    match element_unique f l e with
    | None -> false
    | Some t ->
      (match element_unique f t e with
       | None -> true
       | Some _ -> false)

  let rec double_exists f l =
    match l with
    | [] -> false
    | h :: t ->
      (match element_unique f t h with
       | None -> double_exists f t
       | Some _ -> true
      )

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

  let interset compare l1 l2 =
    let rec aux r = function
      | [] -> r
      | h :: t ->
        if exists (fun y -> compare h y) l2 then aux (h :: r) t
        else aux r t
    in
    aux [] l1

  let remove_duplicates_eq l = remove_duplicates (fun x y -> x == y) l

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

  let choose_list_list ll =
    if List.exists (fun l -> (List.length l) == 0) ll then [] else
      let one_lists, others = List.partition (fun l -> (List.length l) == 1) ll in
      let others = Array.of_list (List.map Array.of_list others) in
      let one_list = List.flatten one_lists in
      let n = Array.length others in
      let idx_max = Array.init n (fun i -> Array.length others.(i)) in
      let idx = Array.init n (fun _ -> 0) in
      let rec increase i =
        if i >= n then None else
        if (idx.(i) + 1) >= idx_max.(i)
        then (Array.set idx i 0; increase (i + 1))
        else (Array.set idx i (idx.(i) + 1); Some ()) in
      let rec aux r =
        let a = List.init n (fun i -> others.(i).(idx.(i))) in
        match increase 0 with
        | None -> a :: r
        | Some _ -> aux (a :: r)
      in
      List.map (fun l -> one_list @ l) (aux [])

  let choose_list_list_order ll =
    if List.exists (fun l -> (List.length l) == 0) ll then [] else
      let others = Array.of_list (List.map Array.of_list ll) in
      let n = Array.length others in
      let idx_max = Array.init n (fun i -> Array.length others.(i)) in
      let idx = Array.init n (fun _ -> 0) in
      let rec increase i =
        if i >= n then None else
        if (idx.(i) + 1) >= idx_max.(i)
        then (Array.set idx i 0; increase (i + 1))
        else (Array.set idx i (idx.(i) + 1); Some ()) in
      let rec aux r =
        let a = List.init n (fun i -> others.(i).(idx.(i))) in
        match increase 0 with
        | None -> a :: r
        | Some _ -> aux (a :: r)
      in
      aux []

  let choose_list_list_order_fold f default ll =
    if List.exists (fun l -> (List.length l) == 0) ll then default else
      let others = Array.of_list (List.map Array.of_list ll) in
      let n = Array.length others in
      let idx_max = Array.init n (fun i -> Array.length others.(i)) in
      let idx = Array.init n (fun _ -> 0) in
      let rec increase i =
        if i >= n then None else
        if (idx.(i) + 1) >= idx_max.(i)
        then (Array.set idx i 0; increase (i + 1))
        else (Array.set idx i (idx.(i) + 1); Some ()) in
      let rec aux r =
        let a = List.init n (fun i -> others.(i).(idx.(i))) in
        match increase 0 with
        | None -> f r a
        | Some _ -> aux (f r a)
      in
      aux default

  let choose_n l n =
    let rec aux r n =
      if n == 0 then r else
        aux (List.flatten @@ List.map (fun e -> List.map (fun r -> e :: r) r) l) (n - 1)
    in
    if n < 0 then raise @@ InterExn "choose_n_eq: bad n"
    else if n == 0 then [[]] else
      aux (List.map (fun x -> [x]) l) (n - 1)

  let choose_n_eq eq l n =
    choose_n (remove_duplicates eq l) n

  let choose_eq_all eq l =
    List.flatten @@
    List.init ((List.length l) + 1) (fun n -> choose_n_eq eq l n)

  let sublist l (s, e) =
    let rec aux r i l =
      if i >= e then r else
        match l with
        | [] -> raise @@ InterExn "sublist"
        | h :: t ->
          if i >= s then
            aux (r @ [h]) (i+1) t
          else
            aux r (i+1) t
    in
    aux [] 0 l

  let filter_mapi f l =
    fold_lefti (fun r i x ->
        match f i x with
        | None -> r
        | Some y -> r @ [y]
      ) [] l

  let lookup eq x l =
    let rec aux i = function
      | [] -> raise @@ InterExn "List.lookup"
      | h :: t -> if eq x h then i else aux (i + 1) t
    in
    aux 0 l

  let nth l i =
    match List.nth_opt l i with
    | Some v -> v
    | None -> raise @@ InterExn "List.nth"

  let power_set_b n =
    let rec aux (cur: bool t t) n: bool t t =
      if n <= 0 then cur else
        aux ((map (fun l -> true:: l) cur) @ (map (fun l -> false:: l) cur)) (n - 1)
    in
    aux [[true]; [false]] (n-1)

  let power_set_b_fold f default n =
    let vec = Array.init n (fun _ -> false) in
    let rec to_zero idx =
      if idx < 0 then () else
        (Array.set vec idx false; to_zero (idx - 1))
    in
    let rec incr idx =
      if idx >= n then false else
      if vec.(idx) then incr (idx + 1) else
        (Array.set vec idx true;
         to_zero (idx - 1);
         (* Printf.printf "vec[0] = %b; vec[1] = %b\n" vec.(0) vec.(1); *)
         true)
    in
    let rec aux r =
      let r = f r vec in
      if incr 0 then aux r else r
    in
    aux default
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
  let layout f tr =
    let rec aux = function
      | Leaf -> "."
      | Node (a, Leaf, Leaf) -> (f a)
      | Node (a, l, r) ->
        Printf.sprintf "{%s, %s, %s}" (aux l) (f a) (aux r)
    in
    aux tr

  let rec leaf eq t u =
    let nochild l r =
      match l, r with
      | Leaf, Leaf -> true
      | _, _ -> false
    in
    match t with
    | Leaf -> false
    | Node (a, l ,r) ->
      ((eq a u) && (nochild l r)) || (leaf eq l u) || (leaf eq r u)

  let rec node eq t u =
    let haschild l r =
      match l, r with
      | Node (_,_,_), _ | _, Node (_,_,_) -> true
      | _, _ -> false
    in
    match t with
    | Leaf -> false
    | Node (a, l ,r) ->
      ((eq a u) && (haschild l r)) || (node eq l u) || (node eq r u)

  let left_child eq t u v =
    let rec aux before t =
      if before then true else
        match t with
        | Leaf -> false
        | Node (a, l, r) ->
          if (eq a u) && (exists (fun x -> eq x v) l) then true else
            aux (aux false l) r
    in
    aux false t

  let right_child eq t u v =
    let rec aux before t =
      if before then true else
        match t with
        | Leaf -> false
        | Node (a, l, r) ->
          if (eq a u) && (exists (fun x -> eq x v) r) then true else
            aux (aux false l) r
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

  let once f tr e =
    let l = flatten tr in
    List.once f l e
end

module LabeledTree = struct
  type ('a, 'b) t =
    | Leaf
    | Node of ('b * 'a * ('a, 'b) t * ('a, 'b) t)

  let rec from_tree label t =
    match t with
    | Tree.Leaf -> Leaf
    | Tree.Node (a, l, r) -> Node(label, a, from_tree label l, from_tree label r)

  let exists f t =
    let rec aux before t =
      if before then true else
        match t with
        | Leaf -> false
        | Node (_, e, l, r) ->
          if f e then true else
            aux (aux before l) r
    in
    aux false t
  let layout f tr =
    let rec aux = function
      | Leaf -> "."
      | Node (_, a, Leaf, Leaf) -> (f a)
      | Node (_, a, l, r) ->
        Printf.sprintf "{%s, %s, %s}" (aux l) (f a) (aux r)
    in
    aux tr

  let rec leaf eq t u =
    let nochild l r =
      match l, r with
      | Leaf, Leaf -> true
      | _, _ -> false
    in
    match t with
    | Leaf -> false
    | Node (_, a, l ,r) ->
      ((eq a u) && (nochild l r)) || (leaf eq l u) || (leaf eq r u)

  let rec node eq t u =
    let haschild l r =
      match l, r with
      | Node (_,_,_,_), _ | _, Node (_,_,_,_) -> true
      | _, _ -> false
    in
    match t with
    | Leaf -> false
    | Node (_, a, l ,r) ->
      ((eq a u) && (haschild l r)) || (node eq l u) || (node eq r u)

  let left_child eq t u v =
    let rec aux before t =
      if before then true else
        match t with
        | Leaf -> false
        | Node (_, a, l, r) ->
          if (eq a u) && (exists (fun x -> eq x v) l) then true else
            aux (aux false l) r
    in
    aux false t

  let right_child eq t u v =
    let rec aux before t =
      if before then true else
        match t with
        | Leaf -> false
        | Node (_, a, l, r) ->
          if (eq a u) && (exists (fun x -> eq x v) r) then true else
            aux (aux false l) r
    in
    aux false t

  let parallel_child eq t u v =
    let rec aux = function
      | Leaf -> false
      | Node (_, _, l, r) ->
        ((exists (fun x -> eq x u) l) && (exists (fun x -> eq x v) r)) || (aux l) || (aux r)
    in
    aux t

  let eq lcompare compare t1 t2 =
    let rec aux = function
      | (Leaf, Leaf) -> true
      | (Node (lab1, a1, l1, r1), Node (lab2, a2, l2, r2)) ->
        if compare a1 a2 && lcompare lab1 lab2 then
          if aux (l1, l2)
          then aux (r1, r2)
          else false
        else false
      | (_, _) -> false
    in
    aux (t1, t2)

  let rec flatten = function
    | Leaf -> []
    | Node (_, a, l, r) -> a::((flatten l) @ (flatten r))
  let flatten_forall compare t =
    List.remove_duplicates compare (flatten t)
  let union l0 l1 = List.union (fun x y -> x == y) l0 l1
  let once f tr e =
    let l = flatten tr in
    List.once f l e
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
  let min_opt l =
    let rec aux m = function
      | [] -> m
      | h :: t -> if h < m then aux h t else aux m t
    in
    match l with
    | [] -> None
    | h :: t -> Some (aux h t)
  let bigger_range l =
    match min_opt l, max_opt l with
    | None, None -> (-1, 1)
    | Some s, Some e -> (s - 1, e + 1)
    | _, _ -> raise @@ InterExn "never happen"
  let of_range (s, e) =
    let len = e - s + 1 in
    List.init len (fun i -> i + s)
end

module StrList = struct
  let eq l1 l2 = List.eq String.equal l1 l2
  let to_string l = List.to_string (fun x -> x) l
  let search errinfo l a =
    List.find errinfo (fun (k,_) -> String.equal k a) l
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

module BitVector = struct
  let to_string bl = String.of_seq
      (List.to_seq (List.map (fun b -> if b then '1' else '0') bl))
  let of_string str = List.map (fun c ->
      match c with
      | '0' -> false
      | '1' -> true
      | _ -> raise @@ InterExn "BitVector") (List.of_seq @@ String.to_seq str)
end

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
let map6 f (a, b, c, d, e, g) = (f a, f b, f c, f d, f e, f g)
let map7 f (a, b, c, d, e, g, h) = (f a, f b, f c, f d, f e, f g, f h)

let time f =
  let t = Sys.time() in
  let fx = f () in
  let delta = (Sys.time() -. t) in
  fx, delta

type compile_tp = Debug | Opt
let ctp = Debug

let clock title f =
  match ctp with
  | Debug ->
    let start_time = Sys.time () in
    let result = f () in
    let end_time = Sys.time () in
    let _ = Printf.printf "delta[%s]:%f\n" title (end_time -. start_time) in
    result
  | Opt -> f ()

open Yojson.Basic
let encode_field_ treetp_name field value =
  `Assoc ["t", `String treetp_name;
          "f", `String field;
          "v", value]
let decode_field_ treetp_name json =
  let open Util in
  let treetp = json |> member "t" |> to_string in
  if String.equal treetp_name treetp then
    let field = json |> member "f" |> to_string in
    let value = json |> member "v" in
    (field, value)
  else raise @@ InterExn (Printf.sprintf "%s::decode wrong type" treetp_name)

let decode_list err decoder json =
  match json with
  | `List l -> List.map decoder l
  | _ -> raise @@ InterExn (Printf.sprintf "decode_list:%s" err)
