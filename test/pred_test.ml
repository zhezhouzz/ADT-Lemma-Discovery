(* module E = Preds.Elem.Elem
 * module P = Preds.Pred.Pred(E)
 * module Tree = Utils.Tree;;
 * module B = Language.Bexpr.Bexpr(Language.Lit.Lit)
 * module Epr = Language.Epr.Epr(B)
 * module D = Axiom.Dtree.Dtree(Epr)(P);;
 * module A = Axiom.Axiom_syn.AxiomSyn(D)(Ml.FastDT.FastDT);;
 * open A.D.P.E;;
 * module PP = A.D.P;; *)
open Printf;;
open Utils;;
open Preds.Pred.Element;;
module P = Preds.Pred.Predicate;;
module A = Axiom.AxiomSyn.Syn;;
module Epr = Language.Ast.SpecAst.E;;
let list_order l u v = "order", l, [I 0; I 1; u; v]
let tree_left t u v = "order", t, [I 0; I 1; u; v]
let tree_right t u v = "order", t, [I 0; I 2; u; v]
let tree_parallel t u v = "order", t, [I 1; I 2; u; v]
;;

let l0 = L [0;1;2] in
let t0_ = (Tree.Node (1,
                      Tree.Node (2, Tree.Leaf, Tree.Leaf),
                      Tree.Node (3, Tree.Leaf, Tree.Leaf)))
in
let t0 = T t0_ in
let exp0 = "member", l0, [I 0] in
let exp1 = "member", l0, [I 1] in
let exp2 = "member", l0, [I 3] in
let exp3 = "member", t0, [I 0] in
let exp4 = "member", t0, [I 1] in
let exp5 = "member", t0, [I 3] in
let exp6 = "list_order", l0, [I 0; I 1] in
let exp7 = "list_order", l0, [I 1; I 0] in
let exp8 = "tree_left", t0, [I 1; I 0] in
let exp9 = "tree_left", t0, [I 1; I 2] in
let exp10 = "tree_right", t0, [I 1; I 2] in
let exp11 = "tree_parallel", t0, [I 2; I 3] in
let exp12 = "tree_parallel", t0, [I 1; I 3] in
let exp13 = "tree_parallel", t0, [I 2; I 1] in
let tests = [exp0;exp1;exp2;exp3;exp4;exp5;exp6;exp7;exp8;exp9;exp10;exp11;exp12;exp13] in
let _ = List.iter (fun exp -> printf "%s=%b\n" (P.apply_layout exp) (P.apply exp)) tests in
let title = ["member", [0]; "member", [1]; "list_order", [0;1]; "==", [0;1]] in
let _ = printf "  \t\t%s\n" (A.layout_title title) in
let pos0 = A.make_sample title l0 [I 0; I 1] in
let pos1 = A.make_sample title (L []) [I 0; I 1] in
let pos2 = A.make_sample title (L [0]) [I 0; I 1] in
let pos3 = A.make_sample title (L [1]) [I 0; I 1] in
let pos4 = A.make_sample title (L [1;0]) [I 0; I 1] in
let neg0 = A.cex_to_sample [I 0; I 1] [false; false; true; false] in
let neg1 = A.cex_to_sample [I 0; I 1] [false; true; true; false] in
let positives = [pos0;pos1;pos2;pos3;pos4] in
let negatives = [neg0;neg1] in
let _ = printf "positive:\n%s" @@
  List.fold_left (fun r s -> sprintf "%s\t%s\n" r (A.layout_sample s)) "" positives in
let _ = printf "negative:\n%s" @@
  List.fold_left (fun r s -> sprintf "%s\t%s\n" r (A.layout_sample s)) "" negatives in
let axiom = A.classify title ~pos:positives ~neg:negatives in
let axiom = A.D.to_forallformula axiom ~dtname:"l" in
let _ = printf "axiom = %s\n" (Epr.layout_forallformula axiom) in
let title2 = A.make_title 2 in
let _ = printf "length(title2) = %i\n" (List.length title2) in
let _ = printf "  \t\t%s\n" (A.layout_title title2) in
();;
