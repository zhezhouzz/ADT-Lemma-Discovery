(**
 * This code as it stands is cryptic. It would be nice to embed some comments
 * along the way to explain what is happening, but for now the best way to
 * understand it is to read the underpinning literature directly.
 *
 * EXPLAIN paper:
 *   https://www.cs.utexas.edu/~isil/cav2013-tool.pdf
 *
 * Simplification Algorithm:
 *   https://theory.stanford.edu/~aiken/publications/papers/sas10.pdf
 *)

open Z3

type node_type =
 | NT_LEAF
 | NT_AND
 | NT_OR

let inspect expr =
  match AST.get_ast_kind (Expr.ast_of_expr expr) with
    | Z3enums.APP_AST ->
       let args = Expr.get_args expr in
       let decl = Expr.get_func_decl expr in
       let decl_name = Symbol.to_string (FuncDecl.get_name decl) in
       (match decl_name with
           | "and" -> (NT_AND, args)
           | "or"  -> (NT_OR, args)
           | _     -> (NT_LEAF, args))
    | _ -> (NT_LEAF, [])

let check_valid ctx expr =
  let solver = Solver.mk_simple_solver ctx in
  let neg = Boolean.mk_not ctx expr in
  let status = Solver.check solver [neg] in
  status == Solver.UNSATISFIABLE

let dda_leaf ctx expr subexpr =
  let nonconstraining = check_valid ctx (Boolean.mk_implies ctx expr subexpr) in
  let nonrelaxing = check_valid ctx (Boolean.mk_implies ctx expr (Boolean.mk_not ctx subexpr)) in
  match (nonconstraining, nonrelaxing) with
  | (true, _) -> Boolean.mk_true ctx
  | (_, true) -> Boolean.mk_false ctx
  | _         -> subexpr

let build_f' f xs = fun ((left, right), result) x ->
  match right with
    | [] ->
       let result' = (f x left) :: result in
       ((x :: left, []), result')
    | (_ :: rs) ->
       let result' = (f x (List.concat [left; right])) :: result in
       ((x :: left, rs), result')

let map_comp_list f lst =
  match lst with
    | [] -> []
    | (_ :: xs) ->
       let f' = build_f' f xs in
       let (_, result) = List.fold_left f' (([], xs), []) lst in
       result

let rec dda_simplify ctx expr subexpr =
  let (ntype, children) = inspect subexpr in
  match ntype with
    | NT_LEAF -> dda_leaf ctx expr subexpr
    | NT_AND  -> Boolean.mk_and ctx (calcC' ctx (fun x -> x) expr children)
    | NT_OR   -> Boolean.mk_or  ctx (calcC' ctx (Boolean.mk_not ctx) expr children)
and calcC' ctx star expr asts =
  (* TODO: this should technically be repeated until fixpoint. *)
  let calcCi' x xs =
    let xs' = List.map star xs in
    let a'  = Boolean.mk_and ctx (expr :: xs') in
    dda_simplify ctx a' x
  in
  map_comp_list calcCi' asts

let nnf ctx expr =
  let nnf_tactic = Tactic.mk_tactic ctx "nnf" in
  let goal = Goal.mk_goal ctx false false false in
  let _ = Goal.add goal [expr] in
  let result = Tactic.apply nnf_tactic goal None in
  let subgoals = Tactic.ApplyResult.get_subgoals result in
  let formulas = List.flatten (List.map (fun sg -> Goal.get_formulas sg) subgoals) in
  Boolean.mk_and ctx formulas

let simplify_wrt (ctx: Z3.context) (wrt: Expr.expr) (expr: Expr.expr) =
  let wrt' = nnf ctx wrt in
  let expr' = nnf ctx expr in
  Expr.simplify (dda_simplify ctx wrt' expr') None
