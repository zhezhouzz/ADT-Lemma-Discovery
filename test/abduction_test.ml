module Ast = Language.Ast.SpecAst
module Value = Preds.Pred.Value

open Ast
open OUnit2
open Utils
open Z3
open Z3.Arithmetic

module SE = E.SE

(* Some simple expressions to aid in test construction. *)
let x      = SE.Var (SE.Int, "x")
let y      = SE.Var (SE.Int, "y")
let list_0 = SE.Var (SE.IntList, "list_0")
let list_1 = SE.Var (SE.IntList, "list_1")
let list_2 = SE.Var (SE.IntList, "list_2")
let zero   = SE.Literal (SE.Int, SE.L.Int 0)
let one    = SE.Literal (SE.Int, SE.L.Int 1)
let two    = SE.Literal (SE.Int, SE.L.Int 2)
let five   = SE.Literal (SE.Int, SE.L.Int 5)
let ten    = SE.Literal (SE.Int, SE.L.Int 10)

(* Helper functions. *)
let set_simple_spec (name: string) (params: string list) (spec: E.t) (map: Ast.spec StrMap.t) =
  StrMap.add name (params, ([], spec)) map
let set_atomic_spec (name: string) (params: string list) (spec: SE.t) (map: Ast.spec StrMap.t) =
  set_simple_spec name params (E.Atom spec) map
let boolop name args = E.Atom (SE.Op (SE.Bool, name, args))
let boolopLit name args = ForAll ([], boolop name args)
let z3_context =
  Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")]

(**
 * QE does not always yield the most parsimonious specifications.
 * Instead of checking for specific spec wordings, just make sure the result
 * is equivalent to the right thing.
 *)
let assert_spec_equiv ctx expected actual =
  let iff = Boolean.mk_iff ctx expected actual in
  let neg = Boolean.mk_not ctx iff in
  let solver = Solver.mk_simple_solver ctx in
  let _ = Solver.add solver [neg] in
  let status = Solver.check solver [] in
  match status with
    | Solver.UNSATISFIABLE -> () (* OK *)
    | _ -> assert_failure ("Specs are not equivalent. "
           ^ "Expected: " ^ (Expr.to_string expected)
           ^ ", Actual: " ^ (Expr.to_string actual))


(*** Begin test suite. ***)

(**
 * If the precondition is not satisfiable, abduction should fail.
 *)
let test_unsat_precondition _ =
  let unsat = E.And [
    (E.Atom (SE.Op (SE.Bool, "==", [x; five])));
    (E.Atom ((SE.Op (SE.Bool, "==", [x; ten]))))
  ] in
  let specs = set_simple_spec "pre" ["x"] unsat StrMap.empty in
  let specs = set_simple_spec "post" [] E.True specs in
  let result = Abduction.abduce z3_context specs (SpecApply ("pre", [x])) (SpecApply ("post", [])) in
  assert_equal (Result.Error "Unsatisfiable Precondition") result

(**
 * No uninterpreted function symbols in pre or post means no abduction needed.
 *)
let test_no_abduction _ =
  let specs = set_atomic_spec "pre"  ["x"] (SE.Op (SE.Bool, "==", [x; five])) StrMap.empty in
  let specs = set_atomic_spec "post" ["x"] (SE.Op (SE.Bool, "<=", [x; ten]))  specs in
  let result = Abduction.abduce z3_context specs (SpecApply ("pre", [x])) (SpecApply ("post", [x])) in
  assert_equal (Result.Ok StrMap.empty) result

(**
 * An abduction problem with one uninterpreted function.
 *)
let test_single_abduction _ =
  let xMinus5 = SE.Op (SE.Bool, "-", [x; five]) in
  let specs = set_atomic_spec "pre"  ["x"] (SE.Op (SE.Bool, "<=", [x; ten])) StrMap.empty in
  let specs = set_atomic_spec "post" ["x"] (SE.Op (SE.Bool, "==", [xMinus5; zero]))  specs in
  (* Query: x <= 10 /\ ??  |=  (x - 5) == 0 *)
  let ctx = z3_context in
  let result = Abduction.abduce ctx specs
                 (And [SpecApply ("pre", [x]); SpecApply ("A", [x])])
                 (SpecApply ("post", [x])) in
  match result with
    | Result.Ok spec_map ->
       (* Expected: Single interpretation, A: x = 5 *)
       let _ = assert_equal 1 (StrMap.cardinal spec_map) in
       let interp = StrMap.find "A" spec_map in
       let expected = Boolean.mk_eq ctx (Integer.mk_const_s ctx "x") (Integer.mk_numeral_i ctx 5) in
       assert_spec_equiv ctx expected interp
    | Result.Error reason -> assert_failure reason

(**
 * A single abduction that involves list encodings.
 *)
let test_list_encoding_sa _ =
  let specs = StrMap.add "R2" (["list_1"; "list_2"],
    (["x"], E.Implies (boolop "member" [list_1; x], boolop "member" [list_2; x]))) StrMap.empty in
  let pre =  And [SpecApply ("R1", [list_1]); SpecApply ("R2", [list_1; list_2])] in
  let post = And [boolopLit "member" [list_1; one];
                  boolopLit "member" [list_2; one]] in
  (*
   * Query:
   *    forall l1 l2. member(l1, x) => member(l2, x)
   *    /\ ??
   *    |=  member(list_1, 1) /\ member(list_2, 1)
   *)
  let ctx = z3_context in
  let result = Abduction.abduce ctx specs pre post in
  match result with
    | Result.Ok spec_map ->
       (* Expected: Single interpretation, R1: member(l1, 1) *)
       let _ = assert_equal 1 (StrMap.cardinal spec_map) in
       let interp = StrMap.find "R1" spec_map in
       let list_sort = Sort.mk_uninterpreted ctx (Symbol.mk_string ctx "list_sort") in
       let list_encoding = FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "list")
           [Integer.mk_sort ctx] list_sort in
       let z3_list_1 = FuncDecl.apply list_encoding [Integer.mk_numeral_i ctx 1] in
       let member = FuncDecl.mk_func_decl ctx (Symbol.mk_string ctx "member")
           [list_sort; Integer.mk_sort ctx] (Boolean.mk_sort ctx) in
       let expected = FuncDecl.apply member [z3_list_1; Integer.mk_numeral_i ctx 1] in
       assert_spec_equiv ctx expected interp
    | Result.Error reason -> assert_failure reason

(**
 * An abduction problem with multiple uninterpreted functions.
 *)
let test_multiple_abduction _ =
  assert_equal true false (* TODO: Implement *)

(**
 * The original test Zhe provided.
 * Commented out for now until the necessary abduction mechanics are in place.
 *)
let test_full _ = ();;
(*
let l0 = Sexpr.Var (Sexpr.IntList, "l0") in
let l1 = Sexpr.Var (Sexpr.IntList, "l1") in
let l2 = Sexpr.Var (Sexpr.IntList, "l2") in
let v1 = Sexpr.Literal (Sexpr.Int, Sexpr.L.Int 1) in
let v2 = Sexpr.Literal (Sexpr.Int, Sexpr.L.Int 2) in
let pre = And [SpecApply ("R1", [l0; l1]); SpecApply ("R2", [l1; l2])] in
let post_forallfomula =
  [],E.And
    [E.Not (E.Atom (Sexpr.Op (Sexpr.Bool, "member", [l1; v1])));
     E.Atom (Sexpr.Op (Sexpr.Bool, "list_order", [l2; v1; v2]))] in
let vc = Implies (pre, SpecApply ("Post", [l0; l1; l2])) in
let _ = printf "vc:\n\t%s\n" @@ layout vc in
let spec_tab = StrMap.empty in
let spec_tab = StrMap.add "Post" (["l0";"l1";"l2"], post_forallfomula) spec_tab in
let _ = printf "where Post:=\n\t%s\n" @@ layout_spec @@ StrMap.find "Post" spec_tab in
let _ = printf "expected result:\n" in
let spec_tab = StrMap.add "R1"
    (["l0"; "l1"], ([], E.Not (E.Atom (Sexpr.Op (Sexpr.Bool, "member", [l1; v1]))))) spec_tab in
let spec_tab = StrMap.add "R2" (["l1"; "l2"],
    (["u"], E.And
       [E.Atom (Sexpr.Op (Sexpr.Bool, "list_order", [l2; v1; v2]));
        E.Implies (E.Atom (Sexpr.Op (Sexpr.Bool, "member", [l1; Sexpr.Var (Sexpr.Int, "u")])),
                     E.Atom (Sexpr.Op (Sexpr.Bool, "member", [l2; Sexpr.Var (Sexpr.Int, "u")])))
       ])) spec_tab in
let _ = printf "R1:=\n\t%s\n" @@ layout_spec @@ StrMap.find "R1" spec_tab in
let _ = printf "R2:=\n\t%s\n" @@ layout_spec @@ StrMap.find "R2" spec_tab in
let value_l0 = Value.L [1;2] in
let value_l1 = Value.L [2] in
let value_l2 = Value.L [2;1;2] in
let env = List.fold_left (fun m (name, v) -> StrMap.add name v m) StrMap.empty
    ["l0", value_l0; "l1", value_l1; "l2", value_l2] in
let _ = printf "eval([1;2],[2],[2;1;2]): %b\n" (exec vc spec_tab env) in
let _ = printf "z3 form:\n" in
let cfg = [("model", "true");
           ("proof", "false");
           ("timeout", "9999")] in
let ctx = (Z3.mk_context cfg) in
let _ = printf "%s:\n\t%s\n"
    (E.layout_forallformula post_forallfomula)
    (Z3.Expr.to_string (E.forallformula_to_z3 ctx post_forallfomula))
in
let _ = printf "%s:\n\t%s\n"
    (layout vc)
    (Z3.Expr.to_string (to_z3 ctx vc spec_tab))
in
let _, neg_vc = neg_to_z3 ctx vc spec_tab in
let _ = printf "neg_vc:\n\t%s\n"
    (Z3.Expr.to_string neg_vc) in
let valid, _ = Solver.check ctx neg_vc in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
();;

(* negation of vc should be unsat, pre should be satisfiable. *)
*)


let suite =
  "AbductionTest" >::: [
      "test_unsat_precondition" >:: test_unsat_precondition;
      "test_no_abduction" >:: test_no_abduction;
      "test_single_abduction" >:: test_single_abduction;
      "test_list_encoding_sa" >:: test_list_encoding_sa;
      "test_multiple_abduction" >:: test_multiple_abduction;
      "test_full" >:: test_full
  ]

let () =
  run_test_tt_main suite
