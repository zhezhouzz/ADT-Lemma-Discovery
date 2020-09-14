module Ast = Language.Ast.SpecAst;;
open Ast;;
open Printf;;
open Utils;;
module Value = Preds.Pred.Element;;
let module Sexpr = E.SE in
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
