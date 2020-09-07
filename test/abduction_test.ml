module A = Language.Ast.Ast(Language.Epr.Epr(Language.Bexpr.Bexpr(Language.Lit.Lit)));;
module Epr = A.E;;
module B = Epr.B;;
open A;;
open Printf;;
let l0 = B.Var (B.IntList, "l0") in
let l1 = B.Var (B.IntList, "l1") in
let l2 = B.Var (B.IntList, "l2") in
let v1 = B.Literal (B.Int, B.L.Int 1) in
let v2 = B.Literal (B.Int, B.L.Int 2) in
let pre = And [SpecApply ("R1", [l0; l1]); SpecApply ("R2", [l1; l2])] in
let post = And
[Not (Atom (B.Op (B.Bool, "member", [l1; v1])));
Atom (B.Op (B.Bool, "list_order", [l2; v1; v2]))] in
let vc = Implies (pre, post) in
let _ = printf "vc:\n%s\n" @@ A.layout vc in
();;

(* negation of vc should be unsat, pre should be satisfiable. *)
