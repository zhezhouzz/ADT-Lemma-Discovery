open Z3
open Z3.Solver
open Z3.Goal
(* open Printf *)
open Utils

let solver_result solver =
  (* let _ = printf "solver_result\n" in *)
  match check solver [] with
  | UNSATISFIABLE -> true, None
  | UNKNOWN ->
    raise (InterExn "time out!")
  (* printf "\ttimeout\n"; false, None *)
  | SATISFIABLE ->
    match Solver.get_model solver with
    | None -> raise (InterExn "never happen")
    | Some m -> false, Some m

let get_int m i =
  match Model.eval m i true with
  | None -> 0
  | Some v ->
    (* printf "get_int(%s)\n" (Expr.to_string i); *)
    int_of_string @@ Arithmetic.Integer.numeral_to_string v

let get_int_name ctx m name =
  get_int m @@ Z3.Arithmetic.Integer.mk_const_s ctx name

let get_pred m predexpr =
  match Model.eval m predexpr true with
  | None -> raise @@ InterExn "get pred"
  | Some v -> (
      match Boolean.get_bool_value v with
      | Z3enums.L_TRUE -> true
      | Z3enums.L_FALSE -> false
      | Z3enums.L_UNDEF -> raise @@ InterExn "get pred"
    )

let check ctx vc =
  (* let _ = printf "check\n" in *)
  let solver = (mk_solver ctx None) in
  let g = (mk_goal ctx true false false) in
  let _ = Goal.add g [vc] in
  let _ = Solver.add solver (get_formulas g) in
  solver_result solver
