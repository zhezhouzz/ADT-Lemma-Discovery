module Ast = Language.Ast.SpecAst;;
open Ast;;
open Printf;;
open Utils;;
module Value = Preds.Pred.Element;;
module A = Axiom.AxiomSyn.Syn;;
module S = Solver;;
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
let _ = printf "whole test\n" in
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
(* let l4 = B.Var (B.IntList, "l4") in *)
let v0 = B.Literal (B.Int, B.L.Int 0) in
let v1 = B.Literal (B.Int, B.L.Int 1) in
let v2 = B.Literal (B.Int, B.L.Int 2) in
let intplus a b = B.Op (B.Int, "+", [a; b]) in
let inteqE a b = E.Atom (B.Op (B.Bool, "==", [a; b])) in
let geE a b = E.Atom (B.Op (B.Bool, ">=", [a; b])) in
let gtE a b = E.Atom (B.Op (B.Bool, ">", [a; b])) in
let ltE a b = E.Atom (B.Op (B.Bool, "<", [a; b])) in
let memberE l u = E.Atom (B.Op (B.Bool, "member", [l; u])) in
let listorderE l u v = E.Atom (B.Op (B.Bool, "list_order", [l; u; v])) in
let specs = [
  "Plus1", (["a";"b"], ([], inteqE b (intplus a v1)));
  "Post", (["a"; "b"; "l0";"l1"],
           (["u"; "v"],
            E.And [
              E.Implies (memberE l0 u, memberE l1 u);
              E.Implies (listorderE l1 u v, geE u v);
              listorderE l1 b a]));
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
let va,vb,vl0,vl1,vl2,vl3,vl4 = clientcode 1 [0] in
let _ = printf "positive sample\n" in
let print_group (va,vb,vl0,vl1,vl2,vl3,vl4) =
  let vl0,vl1,vl2,vl3,vl4 = map5 IntList.to_string (vl0,vl1,vl2,vl3,vl4) in
  printf "a = %i; b = %i\nl0 = [%s]\nl1 = [%s]\nl2 = [%s]\nl3 = [%s]\nl4 = [%s]\n"
    va vb vl0 vl1 vl2 vl3 vl4 in
let _ = print_group (va,vb,vl0,vl1,vl2,vl3,vl4) in
let _ = printf "sample constraint:\n" in
(* let cs = ["l0", vl0; "l1", vl1; "l2", vl2; "l3", vl3; "l4", vl4] in *)
(* let cs = ["l0", vl0; "l1", vl1; "l2", vl2; "l3", vl3;] in *)
let cs = ["l0", vl0] in
let z3u = Z3.Arithmetic.Integer.mk_const_s ctx "u" in
let z3v = Z3.Arithmetic.Integer.mk_const_s ctx "v" in
let z30 = Z3.Arithmetic.Integer.mk_numeral_i ctx 0 in
let z32 = Z3.Arithmetic.Integer.mk_numeral_i ctx 2 in
let uvc = ["u";"v";"l0"], (
    E.And [
      E.Implies (
        E.Or [ltE u v0; gtE u v2; ltE u v0; gtE u v2],
        E.Not (listorderE l0 u v));
      E.Implies (
        E.Or [ltE u v0; gtE u v2],
        E.Not (memberE l0 u))
    ]
  ) in
let uvc = E.forallformula_to_z3 ctx uvc in
let uvc2 = Z3.Boolean.mk_and ctx [
    Z3.Arithmetic.mk_ge ctx z3u z30; Z3.Arithmetic.mk_le ctx z32 z3u;
    Z3.Arithmetic.mk_ge ctx z3v z30; Z3.Arithmetic.mk_le ctx z32 z3v;
    Z3.Boolean.mk_eq ctx (Z3.Arithmetic.Integer.mk_const_s ctx "l0")
      (Z3.Arithmetic.Integer.mk_numeral_i ctx 0);
    Z3.Boolean.mk_eq ctx (Z3.Arithmetic.Integer.mk_const_s ctx "l1")
      (Z3.Arithmetic.Integer.mk_numeral_i ctx 1);
    Z3.Boolean.mk_eq ctx (Z3.Arithmetic.Integer.mk_const_s ctx "l2")
      (Z3.Arithmetic.Integer.mk_numeral_i ctx 2);
    Z3.Boolean.mk_eq ctx (Z3.Arithmetic.Integer.mk_const_s ctx "l3")
      (Z3.Arithmetic.Integer.mk_numeral_i ctx 3);
    Z3.Boolean.mk_eq ctx (Z3.Arithmetic.Integer.mk_const_s ctx "l4")
      (Z3.Arithmetic.Integer.mk_numeral_i ctx 4);
  ] in
let cs = List.map (fun (name, v) ->
    Z3.Boolean.mk_and ctx [
      E.B.fixed_dt_to_z3 ctx "member" name (Value.L v);
      E.B.fixed_dt_to_z3 ctx "list_order" name (Value.L v)
    ]
  ) cs in
let _ = printf "all constraints:\n";
  List.iter (fun e -> printf "%s\n" (Z3.Expr.to_string e)) cs in
let neg_vc_fixed_dt = Z3.Boolean.mk_and ctx (uvc2 :: neg_vc :: cs) in
let _ = printf "neg_vc_fixed_dt:\n\t%s\n"
    (Z3.Expr.to_string neg_vc_fixed_dt) in
let valid, m = Solver.check ctx neg_vc_fixed_dt in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let m = match m with None -> raise @@ InterExn "bad" | Some m -> m in
let get_interpretation ctx m title fv =
  let fv_z3 = List.map (fun fv ->  Z3.Arithmetic.Integer.mk_const_s ctx fv) fv in
  let title_b = List.map (fun feature -> A.D.feature_to_epr feature fv) title in
  let title_z3 = List.map (fun b -> E.B.to_z3 ctx b) title_b in
  List.map (fun z -> S.get_int m z) fv_z3, List.map (fun z -> S.get_pred m z) title_z3
in
let title2 = A.make_title 2 in
let _ = printf "  \t\t%s\n" (A.layout_title title2) in
let fvv, predv = get_interpretation ctx m title2 ["u"; "v"] in
let _ = printf "fv:[%s] pred:[%s]"
    (IntList.to_string fvv) (List.to_string string_of_bool predv) in
();;
