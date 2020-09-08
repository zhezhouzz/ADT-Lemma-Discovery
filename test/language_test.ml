module Ast = Language.Ast.SpecAst;;
module Elem = Preds.Pred.Element;;
open Ast;;
open Printf;;
open Utils;;
let module B = E.B in
(* let l0 = B.Var (B.IntList, "l0") in *)
let l1 = B.Var (B.IntList, "l1") in
let l2 = B.Var (B.IntList, "l2") in
let v1 = B.Literal (B.Int, B.L.Int 1) in
let v2 = B.Literal (B.Int, B.L.Int 2) in
let b0 = B.Op (B.Bool, "==", [v1;v2]) in
let _ = printf "eval(%s) = %b\n" (B.layout b0) (B.exec b0 StrMap.empty) in
let post_forallf =
  [],E.And
    [E.Not (E.Atom (B.Op (B.Bool, "member", [l1; v1])));
     E.Atom (B.Op (B.Bool, "list_order", [l2; v1; v2]))] in
let u = B.Var (B.Int, "u") in
let v = B.Var (B.Int, "v") in
let post_forallf2 =
  ["u"; "v"],E.And
    [E.Not (E.Atom (B.Op (B.Bool, "member", [l1; u])));
     E.Atom (B.Op (B.Bool, "list_order", [l2; u; v]))] in
let post_forallf3 =
  ["u"; "v"],E.Implies
    (E.Atom (B.Op (B.Bool, "list_order", [l2; u; v])),
     (E.Atom (B.Op (B.Bool, "member", [l1; u])))) in
let env = StrMap.add "l1" (Elem.L [1;2]) StrMap.empty in
let env = StrMap.add "l2" (Elem.L [1;2]) env in
let _ = printf "eval(%s) = %b\n"
    (E.layout_forallformula post_forallf)
    (E.forallformula_exec post_forallf env) in
let _ = printf "eval(%s) = %b\n"
    (E.layout_forallformula post_forallf2)
    (E.forallformula_exec post_forallf2 env) in
let _ = printf "eval(%s) = %b\n"
    (E.layout_forallformula post_forallf3)
    (E.forallformula_exec post_forallf3 env) in
();;
