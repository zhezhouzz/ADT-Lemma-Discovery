module type Bexpr = sig
  include BexprTree.BexprTree
  type value = L.value
  val fv: t -> string list
  val type_check : t -> (t * bool)
  val exec: t -> value Utils.StrMap.t -> bool
  val extract_dt: t -> value list * string list
  val to_z3: Z3.context -> t -> Z3.Expr.expr
end

module Bexpr (B: BexprTree.BexprTree): Bexpr = struct
  module P = Preds.Pred.Predicate
  include B
  open Utils
  type value = L.value
  let fv _ = []
  let type_check bexpr = (bexpr, true)
  let non_dt_op op args =
    match op, args with
    | "+", [P.E.I a; P.E.I b] -> Some (P.E.I (a + b))
    | "-", [P.E.I a; P.E.I b] -> Some (P.E.I (a - b))
    | "==", [P.E.I a; P.E.I b] -> Some (P.E.B (a == b))
    | "<>", [P.E.I a; P.E.I b] -> Some (P.E.B (a <> b))
    | ">=", [P.E.I a; P.E.I b] -> Some (P.E.B (a >= b))
    | "<=", [P.E.I a; P.E.I b] -> Some (P.E.B (a <= b))
    | ">", [P.E.I a; P.E.I b] -> Some (P.E.B (a > b))
    | "<", [P.E.I a; P.E.I b] -> Some (P.E.B (a < b))
    | _, _ -> None
  let exec bexpr env =
    let rec aux = function
      | Literal (_, lit) -> L.exec lit
      | Var (_, name) ->
        (match StrMap.find_opt name env with
         | None -> raise @@ InterExn "Bexpr::exec"
         | Some v -> v
        )
      | Op (_, op, args) ->
        let args = List.map aux args in
        (match non_dt_op op args with
         | Some v -> v
         | None -> match args with
           | [] -> raise @@ InterExn "Bexpr::exec"
           | dt :: args -> P.E.B (P.apply (op, dt, args))
        )
    in
    match aux bexpr with
    | P.E.B b -> b
    | _ -> raise @@ InterExn "Bexpr::exec not a bool result"
  let extract_dt bexpr =
    let rec aux = function
      | Literal (_, L.IntList lit) -> [P.E.L lit]
      | Literal (_, L.IntTree lit) -> [P.E.T lit]
      | Op (_, _, args) -> List.concat @@ List.map aux args
      | _ -> []
    in
    let consts = List.remove_duplicates P.E.eq (aux bexpr) in
    let rec aux = function
      | Var (IntList, name) | Var (IntTree, name) -> [name]
      | Op (_, _, args) -> List.concat @@ List.map aux args
      | _ -> []
    in
    let vars = List.remove_duplicates String.equal (aux bexpr) in
    consts, vars

  open Z3aux
  open Z3
  open Arithmetic
  open Boolean
  let non_dt_op_to_z3 ctx op args =
    match op, args with
    | "+", [a; b] -> Some (mk_add ctx [a; b])
    | "-", [a; b] -> Some (mk_sub ctx [a; b])
    | "==", [a; b] -> Some (mk_eq ctx a b)
    | "<>", [a; b] -> Some (mk_not ctx @@ mk_eq ctx a b)
    | ">=", [a; b] -> Some (mk_ge ctx a b)
    | "<=", [a; b] -> Some (mk_le ctx a b)
    | ">", [a; b] -> Some (mk_gt ctx a b)
    | "<", [a; b] -> Some (mk_lt ctx a b)
    | _, _ -> None

  let is_dt = function
    | Int -> false
    | Bool -> false
    | IntList -> true
    | IntTree -> true

  let get_tp = function
    | Literal (tp, _) -> tp
    | Var (tp, _) -> tp
    | Op (tp, _, _) -> tp

  let var_to_z3 ctx tp name =
    match tp with
    | Int -> Integer.mk_const_s ctx name
    | Bool -> Boolean.mk_const_s ctx name
    | IntList | IntTree -> Integer.mk_const_s ctx name

  let predefined_predicates_table ctx =
    let m = StrMap.empty in
    List.fold_left (fun m info ->
        StrMap.add info.P.name
        (FuncDecl.mk_func_decl_s ctx info.P.name
             (List.init (info.P.num_dt + info.P.num_int ) (fun _ -> Integer.mk_sort ctx))
             (Boolean.mk_sort ctx))
          m
      ) m P.raw_preds_info

  let to_z3 ctx b =
    let ptable = predefined_predicates_table ctx in
    let rec aux = function
      | Literal (_, L.Int i) -> int_to_z3 ctx i
      | Literal (_, L.Bool b) -> bool_to_z3 ctx b
      | Literal (_, _) -> raise @@ InterExn "datatype literal"
      | Var (tp, name) -> var_to_z3 ctx tp name
      | Op (_, op, args) ->
        let eargs = List.map aux args in
        if List.exists (fun arg -> is_dt @@ get_tp arg) args
        then
          let pred, args' = P.desugar op in
          let args' = List.map (fun x -> int_to_z3 ctx x) args' in
          match eargs with
          | [] -> raise @@ InterExn "never happend"
          | dt :: args -> FuncDecl.apply (StrMap.find pred ptable) (dt :: (args' @ args))
        else
          (match non_dt_op_to_z3 ctx op eargs with
         | Some e -> e
         | None -> raise @@ InterExn "no such op")
    in
    aux b
end
