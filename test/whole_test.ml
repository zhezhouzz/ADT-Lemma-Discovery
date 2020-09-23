module Ast = Language.SpecAst;;
open Ast;;
open Printf;;
open Utils;;
module Value = Preds.Pred.Value;;
module A = Axiom.AxiomSyn.Syn;;
module S = Solver;;
open Language.Helper;;
let module Sexpr = E.SE in
(* let libcode_cons a l = a :: l in
 * let libcode_sort l = List.sort (fun a b -> -(compare a b)) l in *)
(* let _ = printf "whole test\n" in
 * let a = Sexpr.Var (Sexpr.Int, "a") in
 * let u = Sexpr.Var (Sexpr.Int, "u") in
 * let v = Sexpr.Var (Sexpr.Int, "v") in
 * let l0 = Sexpr.Var (Sexpr.IntList, "l0") in
 * let l1 = Sexpr.Var (Sexpr.IntList, "l1") in
 * let l2 = Sexpr.Var (Sexpr.IntList, "l2") in
 * let l3 = Sexpr.Var (Sexpr.IntList, "l3") in
 * let l4 = Sexpr.Var (Sexpr.IntList, "l4") in
 * let v1 = Sexpr.Literal (Sexpr.Int, Sexpr.L.Int 1) in
 * let intplus a b = Sexpr.Op (Sexpr.Int, "+", [a; b]) in
 * let inteqE a b = E.Atom (Sexpr.Op (Sexpr.Bool, "==", [a; b])) in
 * let geE a b = E.Atom (Sexpr.Op (Sexpr.Bool, ">=", [a; b])) in
 * let memberE l u = E.Atom (Sexpr.Op (Sexpr.Bool, "member", [l; u])) in
 * let listorderE l u v = E.Atom (Sexpr.Op (Sexpr.Bool, "list_order", [l; u; v])) in *)
let vc = Implies (And [SpecApply ("Cons", [a; l0; l1]);
                       SpecApply ("Sort", [l1; l2]);
                       SpecApply ("Cons", [int_plus a const1; l2; l3]);
                       SpecApply ("Sort", [l3; l4]);
                      ], SpecApply ("Post", [a; l0; l4])) in
let specs = [
  "Post", (["a"; "l0";"l1"],
           (["u"; "v"],
            E.And [
              E.Implies (member l0 u, member l1 u);
              E.Implies (list_order l1 u v, int_ge u v);
              E.Implies (
                E.And [int_eq u (int_plus a const1); int_eq v a], list_order l1 u v)]));
  (* The following specs are the result of abduction. *)
  "Cons", (["a";"l0";"l1"],
           (["u"], E.Implies (E.Or [int_eq u a; member l0 u], member l1 u);)
          );
  "Sort", (["l0";"l1"],
           (["u";"v"], E.And [
               E.Implies (member l0 u, member l1 u);
               E.Implies (list_order l1 u v, int_ge u v);
             ])
  )
] in
let spec_tab = List.fold_left
    (fun tab (name, spec) -> StrMap.add name spec tab) StrMap.empty specs in
let cfg = [("model", "true");
               ("proof", "false");
           ("timeout", "9999")] in
let ctx = (Z3.mk_context cfg) in
let _, neg_vc = neg_to_z3 ctx vc spec_tab in
let _ = printf "neg_vc:\n\t%s\n"
    (Z3.Expr.to_string neg_vc) in
let valid, _ = Solver.check ctx neg_vc in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let ax = ["l0";"u";"v"], (
    E.Implies (
      E.And [E.Not (int_eq u v); member l0 u; member l0 v],
              E.Or [list_order l0 u v; list_order l0 v u])
  ) in
let axz3 = E.forallformula_to_z3 ctx ax in
let _ = printf "axiom:\n\t%s\n" (Z3.Expr.to_string axz3) in
let neg_vc_with_ax = Z3.Boolean.mk_and ctx [neg_vc; axz3] in
let valid, _ = Solver.check ctx neg_vc_with_ax in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let axiom = A.axiom_infer ~ctx:ctx ~vc:vc ~spectable:spec_tab
    ~pred_names:["member";"list_order";"=="] ~dttp:E.SE.IntList in
let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in
();;
