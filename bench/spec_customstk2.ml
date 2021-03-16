module Ast = Language.SpecAst
module Value = Pred.Value
module SingleAbd = Inference.SingleAbd;;

open Ast
open Utils
open Z3
open Printf
module SE = E.SE
module T = Tp.Tp
module V = Pred.Value
open Language.Helper
open Bench_utils
open Frontend.Fast.Fast
;;
let ctx = init () in
let x = T.IntList, "x" in
let y = T.IntList, "y" in
let z = T.IntList, "z" in
let u = T.Int, "u" in
let v = T.Int, "v" in
let preds = ["list_member"] in
let bpreds = ["="] in
let list_member a b = E.Atom (SE.Op (T.Int, "list_member", [SE.from_tpedvar a;SE.from_tpedvar b])) in
let f, (fname, fargs) = make_hole "f" [T.IntList; T.IntList] in
let apply_sepc fname = fun args -> Ast.SpecApply (fname, List.map SE.from_tpedvar args) in
let f = apply_sepc "f" in
let assert_pre = apply_sepc "assert_pre" in
let assert_post = apply_sepc "assert_post" in
let spectab = StrMap.empty in
let spectab = StrMap.add "f"
    (fargs, ([u],
             let x = List.nth fargs 0 in
             let y = List.nth fargs 1 in
             E.And [E.Not (list_member x u); E.Not (list_member y u)]
            )) spectab in
let spectab = StrMap.add "assert_pre"
    ([x;z], ([u], list_member x u)) spectab in
let spectab = StrMap.add "assert_post"
    ([x;z], ([u], list_member z u)) spectab in
let post_spec_post = [x;z], ([u],
                             list_member z u
                            ) in
let qv = [u] in
let pre = Ast.And [f [x; y]; f [y; z]] in
let post = Ast.Implies (assert_pre [x;z], assert_post [x;z]) in
let _ = SingleAbd.test ctx preds bpreds pre post qv spectab fname fargs
in
();;
