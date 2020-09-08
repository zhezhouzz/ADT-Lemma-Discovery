module L = Language.Lit.Lit;;
module LS = Language.LitSemantic.LitSemantic(L)(Preds.Pred.Element);;
module B = Language.Bexpr.Bexpr(LS);;
module BS = Language.BexprSemantic.BexprSemantic(B)(LS)(Preds.Pred.Predicate);;
module E = Language.Epr.Epr(BS);;
module ES = Language.EprSemantic.EprSemantic(E)(BS);;
module Ast = Language.Ast.Ast(ES);;
(* module AstS = Language.AstSemantic.AstSemantic(Ast)(ES);; *)
open Printf;;
open Utils;;
let _ = print_endline "langauge" in
let module BS = ES.BS in
(* let l0 = BS.Var (BS.IntList, "l0") in *)
let l1 = BS.Var (BS.IntList, "l1") in
let l2 = BS.Var (BS.IntList, "l2") in
let v1 = BS.Literal (BS.Int, BS.L.Int 1) in
let v2 = BS.Literal (BS.Int, BS.L.Int 2) in
let b0 = BS.Op (BS.Bool, "==", [v1;v2]) in
let _ = printf "eval(%s) = %b\n" (BS.layout b0) (BS.exec b0 StrMap.empty) in
let post_spec =
  [],ES.And
    [ES.Not (ES.Atom (BS.Op (BS.Bool, "member", [l1; v1])));
     ES.Atom (BS.Op (BS.Bool, "list_order", [l2; v1; v2]))] in
let u = BS.Var (BS.Int, "u") in
let v = BS.Var (BS.Int, "v") in
let post_spec2 =
  ["u"; "v"],ES.And
    [ES.Not (ES.Atom (BS.Op (BS.Bool, "member", [l1; u])));
     ES.Atom (BS.Op (BS.Bool, "list_order", [l2; u; v]))] in
let post_spec3 =
  ["u"; "v"],ES.Implies
    (ES.Atom (BS.Op (BS.Bool, "list_order", [l2; u; v])),
     (ES.Atom (BS.Op (BS.Bool, "member", [l1; u])))) in
let env = StrMap.add "l1" (BS.LS.E.L [1;2]) StrMap.empty in
let env = StrMap.add "l2" (BS.LS.E.L [1;2]) env in
let _ = printf "eval(%s) = %b\n"
    (ES.layout_spec post_spec)
    (ES.spec_exec post_spec env) in
let _ = printf "eval(%s) = %b\n"
    (ES.layout_spec post_spec2)
    (ES.spec_exec post_spec2 env) in
let _ = printf "eval(%s) = %b\n"
    (ES.layout_spec post_spec3)
    (ES.spec_exec post_spec3 env) in
();;
