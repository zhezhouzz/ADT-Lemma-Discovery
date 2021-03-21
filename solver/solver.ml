open Z3
open Z3.Solver
open Z3.Goal
open Utils

type smt_result =
  | SmtSat of Model.model
  | SmtUnsat
  | Timeout

let solver_result solver =
  (* let _ = printf "solver_result\n" in *)
  match check solver [] with
  | UNSATISFIABLE -> SmtUnsat
  | UNKNOWN ->
    (* raise (InterExn "time out!") *)
    (* Printf.printf "\ttimeout\n"; *)
    Timeout
  | SATISFIABLE ->
    match Solver.get_model solver with
    | None -> raise (InterExn "never happen")
    | Some m -> SmtSat m

let get_int m i =
  match Model.eval m i true with
  | None -> raise @@ InterExn "get_int"
  | Some v ->
    (* printf "get_int(%s)\n" (Expr.to_string i); *)
    int_of_string @@ Arithmetic.Integer.numeral_to_string v

let get_bool_str m i =
  match Model.eval m i true with
  | None -> "none"
  | Some v -> Expr.to_string v

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

let get_unknown_fv ctx m unknown_fv =
  List.map (fun (_, b) ->
      get_pred m (Boolean.mk_const_s ctx b))
    unknown_fv

let check ctx vc =
  (* let _ = printf "check\n" in *)
  let solver = (mk_solver ctx None) in
  let g = (mk_goal ctx true false false) in
  let _ = Goal.add g [vc] in
  let _ = Solver.add solver (get_formulas g) in
  solver_result solver

type imp_version =
   | V1
   | V2

let impv = V1

let get_preds_interp model =
  match impv with
  | V1 -> [0;1;2;3;4]
  | V2 ->
    let funcs = Model.get_func_decls model in
    let get func =
      match Model.get_func_interp model func with
      | None -> raise @@ InterExn "never happen"
      | Some interp ->
        let bounds =
          List.fold_left (fun l e ->
              Model.FuncInterp.FuncEntry.(
                List.map (fun bound ->
                    if Arithmetic.is_int_numeral bound
                    then int_of_string @@ Arithmetic.Integer.numeral_to_string bound
                    else raise @@ InterExn "bad bound"
                  ) (get_args e)
              ) @ l
            ) [] (Model.FuncInterp.get_entries interp) in
        let bounds = List.remove_duplicates_eq bounds in
        (* let _ = printf "%s\n" (IntList.to_string bounds) in *)
        bounds
    in
    let bounds = List.remove_duplicates_eq @@ List.flatten @@ List.map get funcs in
    match IntList.max_opt bounds with
    | None -> [0]
    | Some ma -> (ma + 1) :: bounds
