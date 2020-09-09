open Utils

type aop = string
type bop = string

type aexpr =
    AInt of int
  | AVar of string
  | Aop of aop * aexpr list
  | AField of string * aexpr
  | AProj of int * aexpr

type bexpr =
  | Bop of bop * aexpr list
	| Member of aexpr * string
	| Link of aexpr * int * int * string * string
  | Next of aexpr * int * int * string * string

let layout_aop op args =
  match op, args with
  | "+", [a; b] -> Printf.sprintf "(%s+%s)" a b
  | "-", [a; b] -> Printf.sprintf "%s-%s" a b
  | _ -> raise @@ ZZExn "layout_aop: undefined"

let rec layout_aexpr = function
  | AInt x -> string_of_int x
  | AVar name -> name
  | Aop (op, args) -> layout_aop op (List.map layout_aexpr args)
  | _ -> raise @@ ZZExn "layout_aexpr: undefined"

let layout_bop op args =
  match op, args with
  | "=", [a; b] -> Printf.sprintf "(%s==%s)" a b
  | "<>", [a; b] -> Printf.sprintf "(%s<>%s)" a b
  | ">=", [a; b] -> Printf.sprintf "(%s>=%s)" a b
  | "<=", [a; b] -> Printf.sprintf "(%s<=%s)" a b
  | ">", [a; b] -> Printf.sprintf "(%s>%s)" a b
  | "<", [a; b] -> Printf.sprintf "(%s<%s)" a b
  | _ -> raise @@ ZZExn "layout_bop: undefined"

let rec layout_bexpr = function
  | Bop (op, args) -> layout_bop op (List.map layout_aexpr args)
	| Member (dt, varname) -> Printf.sprintf "(member %s %s)" (layout_aexpr dt) varname
	| Link (dt, uidx, vidx, u, v) ->
    Printf.sprintf "(link %s (%i:%s) (%i:%s))" (layout_aexpr dt) uidx u vidx v
  | Next (dt, uidx, vidx, u, v) ->
    Printf.sprintf "(next %s (%i:%s) (%i:%s))" (layout_aexpr dt) uidx u vidx v
