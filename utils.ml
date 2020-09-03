exception TestFailedException of string
exception ZZExn of string

module FvMap = Map.Make(String);;
module IntMap = Map.Make(struct type t = int let compare = compare end);;

let contain_i x l =
  match List.find_opt (fun a -> a == x) l with
  | None -> false
  | _ -> true

let contain_l l0 l1 =
  List.for_all (fun x -> contain_i x l1) l0

let rec keep_ord l0 l1 =
  let rec aux a b = function
    | [] -> false
    | h :: t -> if h == a then contain_i b t else aux a b t
  in
  let rec aux2 a = function
    | [] -> true
    | h :: t -> (aux a h l1) && aux2 a t
  in
  match l0 with
  | [] -> true
  | h :: t -> (aux2 h t) && keep_ord t l1

let forall__aux l f =
  let rec aux i = function
    | [] -> true
    | h :: t ->
      if (f h i) then aux (i+1) t else false
  in
  aux 0 l

let forall_ge l =
  forall__aux l (fun h i -> h >= i)
let forall_gt l =
  forall__aux l (fun h i -> h > i)
let forall_eq l =
  forall__aux l (fun h i -> h == i)


let intlist_eq l0 l1 =
  if (List.length l0) <> (List.length l1) then false else
    List.for_all2 (fun a b -> a == b) l0 l1

let list_list_foldl l0 l1 default0 default1 f0 f1 =
  List.fold_left (fun res0 a ->
      f0 res0 (List.fold_left (fun res1 b -> f1 res1 a b) default1 l1)
    ) default0 l0

let list_foldi f default l =
  let rec aux r i = function
    | [] -> r
    | h :: t -> aux (f r i h) (i + 1) t
  in
  aux default 0 l

let list_first l =
  match l with
  | [] -> raise @@ ZZExn "list_first"
  | h :: _ -> h

let list_last l =
  let l = List.rev l in
  match l with
  | [] -> raise @@ ZZExn "list_last"
  | h :: _ -> h

let ll_in_range_first f l0 l1 =
  ((List.length l0) <= (List.length l1)) &&
  list_foldi (fun r i a -> r && (f a (List.nth l1 i))) true l0

let intlist_to_string l =
  list_foldi (fun res i a ->
      if i == 0 then res ^ (string_of_int a) else res ^ ";" ^ (string_of_int a)) "" l

let boollist_to_string l =
  list_foldi (fun res i a ->
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

let inner_list_layout l split default =
  match l with
  | [] -> default
  | h :: t -> List.fold_left (fun res x -> res ^ split ^ x) h t
