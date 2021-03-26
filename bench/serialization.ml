module Ast = Language.SpecAst
module Value = Pred.Value
open Ast
open Utils
open Printf
module SE = E.SE
module L = SE.L
module T = Tp.Tp
;;
let int1 = L.Int 1 in
let btrue = L.Bool true in
let j1 = L.decode @@ L.encode int1 in
let j2 = L.decode @@ L.encode btrue in
let _ = printf "1 := %s; true := %s\n" (L.layout j1) (L.layout j2) in
let varx = SE.Var (T.Int, "x") in
let sum = SE.Op (T.Int, "+", [varx; SE.Literal (T.Int, int1)]) in
let j = SE.encode sum in
(* let _ = printf "sum = %s\n" (Yojson.Basic.pretty_to_string j) in *)
let _ = printf "sum = %s\n" (SE.layout @@ SE.decode j) in
let epr = [T.Int, "x"; T.Int, "y"], E.Implies (E.Atom sum, E.Atom sum) in
let _ = printf "sum = %s\n" (E.layout_forallformula epr) in
let _ = printf "sum = %s\n" (E.layout_forallformula @@
                             E.forallformula_decode @@
                             E.forallformula_encode epr) in
();;
