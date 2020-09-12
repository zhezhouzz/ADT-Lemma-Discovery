module Ast = Language.Ast.SpecAst
module StrSet = Set.Make(String)

open Utils
open Z3
open Z3.Arithmetic
open Z3aux

(**
 * Because of the way the AST is structured, all formula variables should ultimately be
 * introduced by SpecApply. This means we can determine the collection of free variables
 * by combing through the spec and collecting parameters. This is a little hacky. The
 * alternative is to comb through the abduction formula AST and look for variables, which
 * is also a little hacky (and what ORHLE does), as the Z3 API (surprisingly?) does not have
 * a method to get the free variables in a formula.
 *
 * The bottom line is that getting free variables this way is a little quick-and-dirty,
 * and could be improved somewhat by looking at the abduction AST directly if it
 * ever becomes necessary.
 *)
let get_free_variables specs =
  let collect_params _ (params, _) fvs =
    List.fold_left (fun set p -> StrSet.add p set) fvs params
  in
  StrMap.fold collect_params specs StrSet.empty

(** Perform quantifier elimination. *)
let perform_qe ctx quant_vars z3ast =
  let z3_quant_vars = List.map (fun v -> Integer.mk_const_s ctx v) quant_vars in
  let qformula = make_forall ctx z3_quant_vars z3ast in
  let goal = Goal.mk_goal ctx false false false in
  let _ = Goal.add goal [qformula] in
  let qe_tactic = Tactic.mk_tactic ctx "qe" in
  let qe_result = Tactic.apply qe_tactic goal None in
  let subgoals = Tactic.ApplyResult.get_subgoals qe_result in
  let formulas = List.flatten (List.map (fun sg -> Goal.get_formulas sg) subgoals) in
  Expr.simplify (Boolean.mk_and ctx formulas) None

(** Handle the case where we only have a single abducible. *)
let single_abduction ctx specs replacements pre post =
  let abd_name = (Flatten.get_singleton replacements).name in
  let imp = Boolean.mk_implies ctx pre post in
  let free_vars = get_free_variables specs in
  let vbar = StrSet.filter (fun v -> not (StrSet.mem v (Flatten.all_fresh_params replacements))) free_vars in
  (* TODO: MUS filter *)
  let qe_result = perform_qe ctx (StrSet.elements vbar) imp in
  let qe_result = Flatten.replace_backward ctx replacements qe_result in
  let qe_result = Simplify.simplify_wrt ctx pre qe_result in
  Ok (StrMap.add abd_name qe_result StrMap.empty)

(**
 * Handle the case where we have multiple abducibles, but each abducible
 * appears only once.
 *
 * TODO: Deterimine if linear MA is sufficient. If so, implement this. If
 *       not, no need to implement linear version, move on to non-linear
 *       version.
 *)
let linear_multi_abduction ctx specs replacements pre post =
  (* TODO: implement *)
  Ok StrMap.empty

(** The exported abduce function. See module sig for full doc. *)
let abduce (ctx: Z3.context) (specs: (Ast.spec StrMap.t)) (pre: Ast.t) (post: Ast.t) =
  let (z3_pre,  replacements) = Flatten.flatten ctx pre  specs Flatten.empty_replacements in
  let (z3_post, replacements) = Flatten.flatten ctx post specs replacements in

  let pre_sat = Solver.check (Solver.mk_simple_solver ctx) [z3_pre] in
  if pre_sat <> Solver.SATISFIABLE then Result.Error "Unsatisfiable Precondition" else

  match Flatten.abducible_count replacements with
    | 0 -> Ok StrMap.empty (* TODO: make sure pre -> post is satisfiable? *)
    | 1 -> single_abduction ctx specs replacements z3_pre z3_post
    | _ -> linear_multi_abduction ctx specs replacements z3_pre z3_post
