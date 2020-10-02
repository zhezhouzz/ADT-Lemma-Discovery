module type SimpleExpr = sig
  include SimpleExprTree.SimpleExprTree
  type value = L.value
  val fv: t -> string list
  val type_check : t -> (t * bool)
  val exec: t -> value Utils.StrMap.t -> value
  val extract_dt: t -> value list * string list
  val to_z3: Z3.context -> t -> Z3.Expr.expr
  val fixed_int_to_z3: Z3.context -> string -> int -> Z3.Expr.expr
  val fixed_dt_to_z3: Z3.context -> string -> string -> value -> Z3.Expr.expr
  val related_dt: t -> string list -> string list
end

module SimpleExpr (B: SimpleExprTree.SimpleExprTree): SimpleExpr = struct
  module P = Pred.Pred
  module T = Tp.Tp
  include B
  open Utils
  open Printf
  type value = L.value
  let fv _ = []
  let type_check expr = (expr, true)
  let non_dt_op op args =
    match op, args with
    | "+", [P.V.I a; P.V.I b] -> Some (P.V.I (a + b))
    | "-", [P.V.I a; P.V.I b] -> Some (P.V.I (a - b))
    | "==", [P.V.I a; P.V.I b] -> Some (P.V.B (a == b))
    | "<>", [P.V.I a; P.V.I b] -> Some (P.V.B (a <> b))
    | ">=", [P.V.I a; P.V.I b] -> Some (P.V.B (a >= b))
    | "<=", [P.V.I a; P.V.I b] -> Some (P.V.B (a <= b))
    | ">", [P.V.I a; P.V.I b] -> Some (P.V.B (a > b))
    | "<", [P.V.I a; P.V.I b] -> Some (P.V.B (a < b))
    | _, _ -> None
  let exec expr env =
    let rec aux = function
      | Literal (_, lit) -> L.exec lit
      | Var (_, name) -> StrMap.find "SimpleExpr::exec" env name
      | Op (_, op, args) ->
        let args = List.map aux args in
        (match non_dt_op op args with
         | Some v -> v
         | None -> match args with
           | [] -> raise @@ InterExn "SimpleExpr::exec"
           | dt :: args -> P.V.B (P.apply (op, dt, args))
        )
    in
    aux expr
  let extract_dt expr =
    let rec aux = function
      | Literal (_, L.IntList lit) -> [P.V.L lit]
      | Literal (_, L.IntTree lit) -> [P.V.T lit]
      | Op (_, _, args) -> List.concat @@ List.map aux args
      | _ -> []
    in
    let consts = List.remove_duplicates P.V.eq (aux expr) in
    let rec aux = function
      | Var (IntList, name) | Var (IntTree, name) -> [name]
      | Op (_, _, args) -> List.concat @@ List.map aux args
      | _ -> []
    in
    let vars = List.remove_duplicates String.equal (aux expr) in
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
  let var_to_z3 ctx tp name =
    match tp with
    | T.Int -> Integer.mk_const_s ctx name
    | T.Bool -> Boolean.mk_const_s ctx name
    | T.IntList | T.IntTree -> Integer.mk_const_s ctx name

  let bvar_to_z3 ctx = function
    | Var (tp, name) -> var_to_z3 ctx tp name
    | _ -> raise @@ InterExn "bvar_to_z3"

  let predefined_predicates_table ctx =
    let m = StrMap.empty in
    List.fold_left (fun m info ->
        StrMap.add info.P.raw_name
          (FuncDecl.mk_func_decl_s ctx info.P.raw_name
             (List.init info.P.raw_num_args (fun _ -> Integer.mk_sort ctx))
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
        match non_dt_op_to_z3 ctx op eargs with
        | Some e -> e
        | None ->
          (match List.find_opt
                   (fun info -> String.equal info.P.name op) P.preds_info with
          | Some _ ->
            let pred, args' = P.desugar op in
            let args' = List.map (fun x -> int_to_z3 ctx x) args' in
            (match eargs with
             | [] -> raise @@ InterExn "never happend"
             | dt :: args ->
               FuncDecl.apply (StrMap.find "SE:to_z3" ptable pred) (dt :: (args' @ args)))
          | None -> raise @@ InterExn (sprintf "no such op(%s)" op))
    in
    aux b

  let mk_eq_int ctx u i =
    Boolean.mk_eq ctx u (int_to_z3 ctx i)
  let mk_eq_ints ctx us is =
    if (List.length us) != (List.length is) then raise @@ InterExn "mk_eq_ints"
    else Boolean.mk_and ctx (List.map (fun (u, i) -> mk_eq_int ctx u i) (List.combine us is))
  let fixed_dt_to_z3_ ctx pred dt num_int =
    let args = P.fixed_dt_truth_tab pred dt in
    let fv = List.init num_int (fun i -> Var (Int, sprintf "x_%i" i)) in
    let fvz3 = List.map (fun u -> bvar_to_z3 ctx u) fv in
    let right = if (List.length args) == 0 then Boolean.mk_false ctx
      else Boolean.mk_or ctx (List.map (fun arg -> mk_eq_ints ctx fvz3 arg) args) in
    fv, right

  let fixed_dt_to_z3 ctx pred dtname dt =
    match List.find_opt (fun info -> String.equal info.P.name pred) P.preds_info with
    | Some info ->
      if info.P.num_dt != 1 then raise @@ InterExn "not a dt pred" else
        let fv, right = fixed_dt_to_z3_ ctx pred dt info.P.num_int in
        let argdt = Var (IntList, dtname) in
        let left = to_z3 ctx (Op (Bool, pred, argdt :: fv)) in
        make_forall ctx (List.map (fun u -> bvar_to_z3 ctx u) fv)
          (Boolean.mk_iff ctx left right)
    | None -> raise @@ InterExn "no such pred"

  let related_dt expr fv =
    let extract = function
      | Literal (_, _) -> []
      | Var (tp, name) -> [tp, name]
      | Op (_, _, _) -> []
    in
    let rec aux = function
      | Literal (_, _) -> []
      | Var (_, _) -> []
      | Op (_, _, args) ->
        let r = List.flatten (List.map aux args) in
        let argsname = List.flatten (List.map extract args) in
        if List.exists (fun (tp, name) ->
            (T.eq tp T.Int) && (List.exists (fun name' -> String.equal name name') fv)
          ) argsname
        then
          (List.filter_map (fun (tp, name) ->
              if T.is_dt tp then Some name else None
             ) argsname) @ r
        else
          r
    in
    List.remove_duplicates String.equal (aux expr)

  let fixed_int_to_z3 ctx name i =
    to_z3 ctx (Op (Bool, "==", [Var (Int, name); Literal (Int, L.Int i)]))
end
