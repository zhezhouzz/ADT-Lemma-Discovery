module Ast = Language.SpecAst;;
module V = Pred.Value;;
open Ast;;
open Printf;;
open Utils;;
module T = Tp.Tp;;
let module SE = E.SE in
(* let l0 = SE.Var (T.IntList, "l0") in *)
let l1 = SE.Var (T.IntList, "l1") in
let l2 = SE.Var (T.IntList, "l2") in
let v1 = SE.Literal (T.Int, SE.L.Int 1) in
let v2 = SE.Literal (T.Int, SE.L.Int 2) in
let b0 = SE.Op (T.Bool, "==", [v1;v2]) in
let _ = printf "eval(%s) = %s\n" (SE.layout b0) (V.layout @@ SE.exec b0 StrMap.empty) in
let post_forallf =
  [],E.And
    [E.Not (E.Atom (SE.Op (T.Bool, "member", [l1; v1])));
     E.Atom (SE.Op (T.Bool, "list_order", [l2; v1; v2]))] in
let u = SE.Var (T.Int, "u") in
let v = SE.Var (T.Int, "v") in
let post_forallf2 =
  ["u"; "v"],E.And
    [E.Not (E.Atom (SE.Op (T.Bool, "member", [l1; u])));
     E.Atom (SE.Op (T.Bool, "list_order", [l2; u; v]))] in
let post_forallf3 =
  ["u"; "v"],E.Implies
    (E.Atom (SE.Op (T.Bool, "list_order", [l2; u; v])),
     (E.Atom (SE.Op (T.Bool, "member", [l1; u])))) in
let env = StrMap.add "l1" (V.L [1;2]) StrMap.empty in
let env = StrMap.add "l2" (V.L [1;2]) env in
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
