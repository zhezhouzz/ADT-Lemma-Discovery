(**
 * Part of multiabduction is "flattening" abduction queries so that all
 * abducibles appear at the top-level instead of embedded in internal
 * clauses. This is accomplished by replacing all abducibles R(x)
 * with x' == x for fresh x', and adding a fresh R'(x') at the top level.
 *
 * See Albarghouthi et al. for more details on this procedure:
 * http://pages.cs.wisc.edu/~aws/papers/popl16.pdf
 *
 * This module provides utilities for flattening and tracking fresh
 * variable replacements.
 *)

module AbdMap = Map.Make(Abducible)
module Ast = Language.SpecAst
module StrSet = Set.Make(String)

open Utils
open Z3
open Z3.Arithmetic
open Z3aux

(**
 * A record of the variable and abducible replacements made during a
 * flattening.
 *)
type abd_replacements = {
  orig_to_fresh : Abducible.t AbdMap.t;
  fresh_to_orig : Abducible.t AbdMap.t;
}

let empty_replacements = {
  orig_to_fresh = AbdMap.empty;
  fresh_to_orig = AbdMap.empty;
}

(** Get a fresh variable name from Z3. *)
let freshen (ctx: Z3.context) (name: string) =
  let freshExpr = Expr.mk_fresh_const ctx name (Integer.mk_sort ctx) in
  Expr.to_string freshExpr

(**
 * If the given abducible is in the given replacements mapping, retrieve its
 * fresh replacement. Otherwise, add a new fresh replacement.
 *
 * Returns both the replacement abducible and the (potentially modified)
 * replacements mapping.
 *)
let find_or_add (ctx: Z3.context) (abd: Abducible.t) (replacements: abd_replacements) =
  match AbdMap.find_opt abd replacements.orig_to_fresh with
    | Some fresh_abd -> (fresh_abd, replacements)
    | None ->
       let fresh_name = freshen ctx abd.name in
       let fresh_params = List.map (fun (name, indexed, sort) -> (freshen ctx name, indexed, sort)) abd.params in
       let fresh_abd = { Abducible.name = fresh_name; Abducible.params = fresh_params } in
       let replacements' = {
           orig_to_fresh = AbdMap.add abd fresh_abd replacements.orig_to_fresh;
           fresh_to_orig = AbdMap.add fresh_abd abd replacements.fresh_to_orig;
         } in
       (fresh_abd, replacements')

(** Returns the number of abducibles in the replacement mapping. *)
let abducible_count (replacements: abd_replacements) =
  AbdMap.cardinal replacements.orig_to_fresh

(**
 * Gets the single original abducible from the replacement mapping.
 * Raises an exception if the replacement mapping has zero or more
 * than one elements.
 *)
let get_singleton (replacements: abd_replacements) =
  match AbdMap.bindings replacements.orig_to_fresh with
    | (abd, _) :: [] -> abd
    | _ -> raise (Failure "replacements mapping is not a singleton")

(** Returns a set of all fresh parameter names in the entire replacement mapping. *)
let all_fresh_param_names (replacements: abd_replacements) =
  let collect_params (abd: Abducible.t) _ param_set =
    List.fold_left (fun set (name, _, _) -> StrSet.add name set) param_set abd.params
  in
  AbdMap.fold collect_params replacements.fresh_to_orig StrSet.empty

(**
 * Reverses variable replacement in the given Z3 expression. All occurences of fresh
 * parameter names in the expression are replaced by the corresponding parameter name
 * from the original abducible.
 *)
let replace_backward (ctx: Z3.context) (replacements: abd_replacements) (expr: Expr.expr) =
  let rev_map (fresh_abd: Abducible.t) (orig_abd: Abducible.t) (fparams, oparams) =
    let pairs = List.combine fresh_abd.params orig_abd.params in
    List.fold_left (fun (fp, op) (fv, ov) -> (fv :: fp, ov :: op)) (fparams, oparams) pairs
  in
  let (fparams, oparams) = AbdMap.fold rev_map replacements.fresh_to_orig ([], []) in
  (* TODO: This shouldn't always be an integer constant. *)
  let to_consts params = List.map (fun (p, _, _) -> Integer.mk_const_s ctx p) params in
  Expr.substitute expr (to_consts fparams) (to_consts oparams)


(**
  * A temporary hack to extract parameter names from simple expressions.
  * Assumes all parameters are int vars and
  * --> CRASHES ON ANYTHING ELSE! <--
  *
  * A more general solution is to transform all abducibles as:
  *  1. A(se1, se2, ...) becomes A(x1, x2, ...)
  *  2. Add x1 = se1 /\ x2 = se2 /\ ... to the abduction precondition
  *
  * This assumes all SEs are expressible in our Z3 theory, which they
  * should be.
  *)
let extract_params_HACK ctx (ses: Ast.E.SE.t list) =
  let extract se = match se with
    | Ast.E.SE.Var (Ast.E.SE.Int, x)     -> (x, false, Integer.mk_sort ctx)
    | Ast.E.SE.Var (Ast.E.SE.IntList, x) -> (x, true, make_uninterpreted_sort ctx "list")
    | _ -> raise @@ Failure ("Abduction is currently unable to handle the type of this parameter: "
                           ^ (Ast.E.SE.layout se))
  in
  List.map extract ses


(**
 * When flattening, we replace all function occurences A(x1, x2, ...) with the
 * constraint that the function args equal the fresh args in the top-level replacement
 * abducible, e.g. x1 = x1' /\ x2 = x2' /\ ... for fresh x1', x2', ...
 *
 * This function constructs such an equivalence clause for the given parameter lists.
 *)
let fresh_params_equiv_clause (ctx: Z3.context) (orig_params: Abducible.param_t list) (fresh_params: Abducible.param_t list) =
  let make_fresh_equiv (orig_param, fresh_param) =
    let z3_orig_param  = Abducible.param_to_z3 ctx orig_param  in
    let z3_fresh_param = Abducible.param_to_z3 ctx fresh_param in
    Boolean.mk_eq ctx z3_orig_param z3_fresh_param
  in
  let fresh_equivs = List.map make_fresh_equiv (List.combine orig_params fresh_params) in
  Boolean.mk_and ctx fresh_equivs

(**
 * Performs the flattening operation.
 *
 * Accepts a SpecAST, a specification mapping, and a mapping of any replacements
 * that have already been made as part of the larger abduction problem. Returns
 * a Z3 expression without any uninterpreted function calls along with a mapping of
 * the generated top-level abducibles.
 *
 * This flattening operation treats any SpecApply in the AST that is not present in
 * the specification mapping as an abducible.
 *)
let flatten (ctx: Z3.context) (ast: Ast.t) (specs: (Ast.spec StrMap.t)) (replacements: abd_replacements) =
  let rec to_z3 ast replacements =
    match ast with
    | Ast.ForAll forallf ->
       (Ast.E.forallformula_to_z3 ctx forallf, replacements)
    | Ast.Implies (p1, p2) ->
       let (z3_p1, replacements) = to_z3 p1 replacements in
       let (z3_p2, replacements) = to_z3 p2 replacements in
       (Boolean.mk_implies ctx z3_p1 z3_p2, replacements)
    | Ast.Ite (p1, p2, p3) ->
       let (z3_p1, replacements) = to_z3 p1 replacements in
       let (z3_p2, replacements) = to_z3 p2 replacements in
       let (z3_p3, replacements) = to_z3 p3 replacements in
       (Boolean.mk_ite ctx z3_p1 z3_p2 z3_p3, replacements)
    | Ast.Not p ->
       let (z3_p, replacements) = to_z3 p replacements in
       (Boolean.mk_not ctx z3_p, replacements)
    | Ast.And ps ->
       let aux (ast_list, replacements) ast =
         let (z3_ast, replacements) = to_z3 ast replacements in
         (z3_ast :: ast_list, replacements)
       in
       let (z3_ps, replacements) = List.fold_left aux ([], replacements) ps in
       (Boolean.mk_and ctx z3_ps, replacements)
    | Ast.Or ps ->
       let aux (ast_list, replacements) ast =
         let (z3_ast, replacements) = to_z3 ast replacements in
         (z3_ast :: ast_list, replacements)
       in
       let (z3_ps, replacements) = List.fold_left aux ([], replacements) ps in
       (Boolean.mk_or ctx z3_ps, replacements)
    | Ast.Iff (p1, p2) ->
       let (z3_p1, replacements) = to_z3 p1 replacements in
       let (z3_p2, replacements) = to_z3 p2 replacements in
       (Boolean.mk_iff ctx z3_p1 z3_p2, replacements)
    | Ast.SpecApply (name, params) ->
       match StrMap.find_opt name specs with
       | None ->
          let eparams = extract_params_HACK ctx params in
          let abd = { Abducible.name = name; Abducible.params = eparams } in
          let (fresh_abd, replacements) = find_or_add ctx abd replacements in
          (fresh_params_equiv_clause ctx eparams fresh_abd.params, replacements)
       | Some (_, forallf) ->
          let spec_z3 = Ast.E.forallformula_to_z3 ctx forallf in
          (spec_z3, replacements)
  in
  to_z3 ast replacements
