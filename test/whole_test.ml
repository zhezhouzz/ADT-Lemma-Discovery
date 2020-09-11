module Ast = Language.Ast.SpecAst;;
open Ast;;
open Printf;;
open Utils;;
module Value = Preds.Pred.Element;;
let module B = E.B in
let libcode_cons a l = a :: l in
let libcode_sort l = List.sort (fun a b -> -(compare a b)) l in
let clientcode a l0 =
  let b = a + 1 in
  let l1 = libcode_cons a l0 in
  let l2 = libcode_sort l1 in
  let l3 = libcode_cons b l2 in
  let l4 = libcode_sort l3 in
  a,b,l0,l1,l2,l3,l4
in
let vc = Implies (And [SpecApply ("Cons", ["a"; "l0"; "l1"]);
                       SpecApply ("Sort", ["l1"; "l2"]);
                       SpecApply ("Plus1", ["a"; "b"]);
                       SpecApply ("Cons", ["b"; "l2"; "l3"]);
                       SpecApply ("Sort", ["l3"; "l4"]);
                      ], SpecApply ("Post", ["a"; "b"; "l0"; "l4"])) in
let a = B.Var (B.Int, "a") in
let b = B.Var (B.Int, "b") in
let u = B.Var (B.Int, "u") in
let v = B.Var (B.Int, "v") in
let l0 = B.Var (B.IntList, "l0") in
let l1 = B.Var (B.IntList, "l1") in
(* let l2 = B.Var (B.IntList, "l2") in
 * let l3 = B.Var (B.IntList, "l3") in *)
let l4 = B.Var (B.IntList, "l4") in
let v1 = B.Literal (B.Int, B.L.Int 1) in
let intplus a b = B.Op (B.Int, "+", [a; b]) in
let inteqE a b = E.Atom (B.Op (B.Bool, "==", [a; b])) in
let geE a b = E.Atom (B.Op (B.Bool, ">=", [a; b])) in
let memberE l u = E.Atom (B.Op (B.Bool, "member", [l; u])) in
let listorderE l u v = E.Atom (B.Op (B.Bool, "list_order", [l; u; v])) in
let specs = [
  "Plus1", (["a";"b"], ([], inteqE b (intplus a v1)));
  "Post", (["a"; "b"; "l1";"l2"],
           (["u"; "v"],
            E.And [
              E.Implies (memberE l0 u, memberE l4 u);
              E.Implies (listorderE l4 u v, geE u v);
              listorderE l4 b a]));
  (* The following specs are the result of abduction. *)
  "Cons", (["a";"l0";"l1"],
           (["u"], E.Implies (E.Or [inteqE u a; memberE l0 u], memberE l1 u);)
          );
  "Sort", (["l0";"l1"],
           (["u";"v"], E.And [
               E.Implies (memberE l0 u, memberE l1 u);
               E.Implies (listorderE l1 u v, geE u v);
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
      E.And [E.Not (inteqE u v); memberE l0 u; memberE l0 v],
              E.Or [listorderE l0 u v; listorderE l0 v u])
  ) in
let axz3 = E.forallformula_to_z3 ctx ax in
let _ = printf "axiom:\n\t%s\n" (Z3.Expr.to_string axz3) in
let neg_vc_with_ax = Z3.Boolean.mk_and ctx [neg_vc; axz3] in
let valid, _ = Solver.check ctx neg_vc_with_ax in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let va,vb,vl0,vl1,vl2,vl3,vl4 = clientcode 1 [] in
let _ = printf "positive sample\n" in
let print_group (va,vb,vl0,vl1,vl2,vl3,vl4) =
  let vl0,vl1,vl2,vl3,vl4 = map5 IntList.to_string (vl0,vl1,vl2,vl3,vl4) in
  printf "a = %i; b = %i\nl0 = [%s]\nl1 = [%s]\nl2 = [%s]\nl3 = [%s]\nl4 = [%s]\n"
    va vb vl0 vl1 vl2 vl3 vl4 in
let _ = print_group (va,vb,vl0,vl1,vl2,vl3,vl4) in
let _ = printf "sample constraint:\n" in
let c = E.B.fixed_dt_to_z3 ctx "list_order" "l3" (Value.L [1;2]) in
let _ = printf "list_order([1;2], x_0, x_1):\n\t%s\n" (Z3.Expr.to_string c) in
let c = E.B.fixed_dt_to_z3 ctx "member" "l3" (Value.L [1;2]) in
let _ = printf "member([1;2], x_0):\n\t%s\n" (Z3.Expr.to_string c) in
();;
