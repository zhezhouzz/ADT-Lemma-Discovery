(**
 * Represents an uninterpreted function application for which we will abduce
 * an interpretation.
 *)

type param_t = string * bool * Z3.Sort.sort
type t = {name: string; params: param_t list }

let compare_params ((p1, _, _): param_t) ((p2, _, _): param_t) = compare p1 p2

let compare_param_lists (params1: param_t list) (params2: param_t list) =
  match List.compare_lengths params1 params2 with
  | 0 ->
     let comp_param c (p1, p2) = if c <> 0 then compare_params p1 p2 else c in
     List.fold_left comp_param 0 (List.combine params1 params1)
  | c -> c

let compare (abd1: t) (abd2: t) =
  match compare abd1.name abd2.name with
  | 0 -> compare_param_lists abd1.params abd2.params
  | c -> c

let param_to_z3 ctx ((name, indexed, sort): param_t) =
  match indexed with
    | false ->
      Z3.Expr.mk_const ctx (Z3.Symbol.mk_string ctx name) sort
    | true ->
      let sort_name = Z3.Symbol.get_string (Z3.Sort.get_name sort) in
      let value_func_name = Z3.Symbol.mk_string ctx (sort_name ^ "_value") in
      let index = Z3.Arithmetic.Integer.mk_const ctx (Z3.Symbol.mk_string ctx name) in
      let value_func = Z3.FuncDecl.mk_func_decl ctx value_func_name
          [Z3.Arithmetic.Integer.mk_sort ctx] sort in
      Z3.FuncDecl.apply value_func [index]

module ParamSet = Set.Make(struct type t = param_t let compare = compare_params end)
