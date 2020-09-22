module Ast = Language.SpecAst
module Value = Preds.Pred.Value

open Ast
open OUnit2
open Utils
open Z3
open Z3.Arithmetic
open Printf
module SE = E.SE

(* Some simple literals to aid in test construction. *)
let l0    = SE.Var (SE.Int, "l0")
let l1    = SE.Var (SE.Int, "l1")
let l2    = SE.Var (SE.Int, "l2")
let u    = SE.Var (SE.Int, "u")
let one = SE.Literal (SE.Int, SE.L.Int 1)
let two = SE.Literal (SE.Int, SE.L.Int 2)
let member l u = SE.Op (SE.Bool, "member", [l; u])
let list_order l u v = SE.Op (SE.Bool, "list_order", [l; u; v])

(* Helper functions. *)
let set_simple_spec (name: string) (params: string list) (spec: E.t) (map: Ast.spec StrMap.t) =
  StrMap.add name (params, ([], spec)) map
let set_atomic_spec (name: string) (params: string list) (spec: SE.t) (map: Ast.spec StrMap.t) =
  set_simple_spec name params (E.Atom spec) map
let z3_context =
  Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")]
let assert_spec_equiv ctx expected actual =
  let iff = Boolean.mk_iff ctx expected actual in
  let neg = Boolean.mk_not ctx iff in
  let solver = Solver.mk_simple_solver ctx in
  let status = Solver.check solver [neg] in
  match status with
  | Solver.UNSATISFIABLE -> () (* OK *)
  | _ -> printf "actual = %s\n" (Expr.to_string actual);
    assert_failure "specs are not equivalent"
;;
(* let specs = StrMap.add "R1"
 *     (["l0"; "l1"], ([], E.Not (E.Atom (member l1 u)))) StrMap.empty in *)
let specs = StrMap.add "R2"
    (["l1"; "l2"],
     (["u"], E.And
        [E.Atom (list_order l2 one two);
         E.Implies (E.Atom (member l1 u), E.Atom (member l2 u))
        ])) StrMap.empty in
let specs = StrMap.add "Post"
    (["l1"; "l2"],
     ([],E.And
        [E.Not (E.Atom (member l1 one));
         E.Atom (list_order l2 one two)])
    ) specs in
let ctx = z3_context in
let result = Abduction.abduce ctx specs
    (And [SpecApply ("R1", [l0;l1]); SpecApply ("R2", [l1;l2])])
    (SpecApply ("Post", [l1;l2])) in
let _ = printf "R2:%s\n"
    (Expr.to_string @@ E.forallformula_to_z3 ctx @@ snd @@ StrMap.find "R2" specs) in
match result with
| Result.Ok spec_map ->
  (* Expected: Single interpretation, A -> x = 5 *)
  let _ = assert_equal 1 (StrMap.cardinal spec_map) in
  let expected = Boolean.mk_eq ctx (Integer.mk_const_s ctx "x") (Integer.mk_numeral_i ctx 5) in
  let interp = StrMap.find "R1" spec_map in
  assert_spec_equiv ctx expected interp
| Result.Error reason -> assert_failure reason
;;
