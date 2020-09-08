module A = Language.Ast.Ast(Language.Epr.Epr(Language.Bexpr.Bexpr(Language.Lit.Lit)));;
module Epr = A.E;;
module B = Epr.B;;
open A;;
open Printf;;
open Utils;;
let l0 = B.Var (B.IntList, "l0") in
let l1 = B.Var (B.IntList, "l1") in
let l2 = B.Var (B.IntList, "l2") in
let v1 = B.Literal (B.Int, B.L.Int 1) in
let v2 = B.Literal (B.Int, B.L.Int 2) in
let pre = And [SpecApply ("R1", [l0; l1]); SpecApply ("R2", [l1; l2])] in
let post_spec =
  [],Epr.And
    [Epr.Not (Epr.Atom (B.Op (B.Bool, "member", [l1; v1])));
     Epr.Atom (B.Op (B.Bool, "list_order", [l2; v1; v2]))] in
let vc = Implies (pre, SpecApply ("Post", [l0; l1; l2])) in
let _ = printf "vc:\n\t%s\n" @@ A.layout vc in
let spec_tab = StrMap.empty in
let spec_tab = StrMap.add "Post" post_spec spec_tab in
let _ = printf "where Post:=\n\t%s\n" @@ Epr.layout_spec @@ StrMap.find "Post" spec_tab in
let _ = printf "expected result:\n" in
let spec_tab = StrMap.add "R1"
    ([], Epr.Not (Epr.Atom (B.Op (B.Bool, "member", [l1; v1])))) spec_tab in
let spec_tab = StrMap.add "R2"
    (["u"], Epr.And
       [Epr.Atom (B.Op (B.Bool, "list_order", [l2; v1; v2]));
        Epr.Implies (Epr.Atom (B.Op (B.Bool, "member", [l1; B.Var (B.Int, "u")])),
                     Epr.Atom (B.Op (B.Bool, "member", [l2; B.Var (B.Int, "u")])))
       ]) spec_tab in
let _ = printf "R1:=\n\t%s\n" @@ Epr.layout_spec @@ StrMap.find "R1" spec_tab in
let _ = printf "R2:=\n\t%s\n" @@ Epr.layout_spec @@ StrMap.find "R2" spec_tab in
();;

(* negation of vc should be unsat, pre should be satisfiable. *)
