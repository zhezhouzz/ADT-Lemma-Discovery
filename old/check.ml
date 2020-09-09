open Z3
open Z3.Solver
open Z3.Goal
open Z3aux
open Printf
open Utils

let solver_result ctx solver =
  match check solver [] with
  | UNSATISFIABLE -> true, None
  | UNKNOWN ->
    (* raise (TestFailedException "time out!") *)
  printf "\ttimeout\n"; false, None
  | SATISFIABLE ->
    match Solver.get_model solver with
    | None -> raise (TestFailedException "")
    | Some m -> false, Some m

let get_int m i =
  match Model.eval m i true with
  | None -> 0
  | Some v ->
    (* printf "get_int(%s)\n" (Expr.to_string i); *)
    int_of_string @@ Arithmetic.Integer.numeral_to_string v

let get_int_name ctx m name =
  get_int m @@ Z3.Arithmetic.Integer.mk_const_s ctx name

let get_list ctx m l length =
  let len = get_int m length in
  let _ = Printf.printf "get_list(%s %i)\n" (Expr.to_string l) len in
  let res = List.init len (fun i ->
      get_int m (Z3Array.mk_select ctx l (int_to_z3 ctx i))
    )
  in
  res

let get_list_name ctx m name =
  get_list ctx m
    (Z3.Z3Array.mk_const_s ctx (name ^"_a")
       (Z3.Arithmetic.Integer.mk_sort ctx)
       (Z3.Arithmetic.Integer.mk_sort ctx))
    (Z3.Arithmetic.Integer.mk_const_s ctx (name ^ "_length"))

let check ctx vc =
  let solver = (mk_solver ctx None) in
  let g = (mk_goal ctx true false false) in
  let _ = Goal.add g [vc] in
  let _ = Solver.add solver (get_formulas g) in
  solver_result ctx solver
