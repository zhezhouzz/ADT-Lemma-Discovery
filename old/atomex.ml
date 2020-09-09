open Utils
open Atom

let aop_excute op args =
  match op, args with
  | "+", [a; b] -> a + b
  | "-", [a; b] -> a - b
  | _ -> raise @@ ZZExn "aop_excute: undefined"

let aexpr_excute m a =
  let rec aux = function
    | AInt x -> x
    | AVar name ->
      (match FvMap.find_opt name m with
       | None -> raise @@ ZZExn "aexpr_excute"
       | Some x -> x
      )
    | Aop (op, args) -> aop_excute op (List.map aux args)
    | _ -> raise @@ ZZExn "aexpr_excute: undefined"
  in
  aux a

let bop_excute op args =
  match op, args with
  | "=", [a; b] -> a == b
  | "<>", [a; b] -> a <> b
  | ">=", [a; b] -> a >= b
  | "<=", [a; b] -> a <= b
  | ">", [a; b] -> a > b
  | "<", [a; b] -> a < b
  | _ -> raise @@ ZZExn "bop_excute: undefined"


type dtexec = {member: int -> bool;
               link: int -> int -> int -> int -> bool;
               next: int -> int -> int -> int -> bool}

let member_exec dt x =
  match IntMap.find_opt x dt with
  | None -> false
  | Some _ -> true

let link_exec dt _ _ x y =
  if x = y
  then
    match IntMap.find_opt x dt with
    | None -> false
    | Some idxs -> (List.length idxs) >= 2
  else
    match IntMap.find_opt x dt, IntMap.find_opt y dt with
    | None, _ -> false
    | _, None -> false
    | Some xidxs, Some yidxs -> (list_last xidxs) < (list_first yidxs)

let next_exec dt _ _ x y =
  if x = y
  then
    match IntMap.find_opt x dt with
    | None -> false
    | Some idxs -> (List.length idxs) >= 2
  else
    match IntMap.find_opt x dt, IntMap.find_opt y dt with
    | None, _ -> false
    | _, None -> false
    | Some xidxs, Some yidxs ->
      let xidxs = List.map (fun x -> x + 1) xidxs in
      not (check_list_unique (fun x y -> x == y) (xidxs @ yidxs))

let list_to_dtexec l =
  let dt = IntMap.empty in
  let aux dt idx x =
    match IntMap.find_opt x dt with
    | None -> IntMap.add x [idx] dt
    | Some idxs -> IntMap.add x (idx::idxs) dt
  in
  let intmap = list_foldi aux dt l in
  {member = member_exec intmap;
   link = link_exec intmap;
   next = next_exec intmap}

let bexpr_excute mdt mi b =
  let handle = function
    | AVar name ->
      (match FvMap.find_opt name mdt with
       | None -> raise @@ ZZExn "error in bexpr exec"
       | Some p -> p
      )
    | _ -> raise @@ ZZExn "undefined in bexpr exec" in
  let rec aux = function
    | Bop (op, args) -> bop_excute op (List.map (fun x -> aexpr_excute mi x) args)
	  | Member (dt, varname) ->
      let p = handle dt in
      let v = aexpr_excute mi (AVar varname) in
      p.member v
	  | Link (dt, uidx, vidx, u, v) ->
      let p = handle dt in
      let u, v = map_double (fun x -> aexpr_excute mi (AVar x)) (u, v) in
      p.link uidx vidx u v
    | Next (dt, uidx, vidx, u, v) ->
      let p = handle dt in
      let u, v = map_double (fun x -> aexpr_excute mi (AVar x)) (u, v) in
      p.next uidx vidx u v
  in
  aux b
