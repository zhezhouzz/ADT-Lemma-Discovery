module Ast = Language.SpecAst
module Value = Preds.Pred.Value
module S = Solver;;
module A = Axiom.AxiomSyn.Syn;;

open Ast
open Utils
open Z3
open Printf
module SE = E.SE
;;
(* let snoc (lenf, f, lenr, r) x =
 *   let lenr = lenr + 1 in
 *   let r = lazy (Cons (x, r)) in
 *   if lenr <= lenf then (lenf, f, lenr, r)
 *   else (lenf + lenr, f ++ reverse r, 0, lazy Nil) *)
open Language.Helper;;
let cons h t l = SpecApply ("Cons", [h;t;l]) in
let nil l = SpecApply ("Nil", [l]) in
let snoc lenf f lenr r x lenf' f' lenr' r' =
  SpecApply ("Snoc", [lenf;f;lenr;r;x;lenf';f';lenr';r']) in
let liblazy l1 l2 = SpecApply ("Lazy", [l1;l2]) in
let reverse l1 l2 = SpecApply ("Reverse", [l1;l2]) in
let concat l1 l2 l3 = SpecApply ("Concat", [l1;l2;l3]) in
let plus x y z = SpecApply ("Plus", [x;y;z]) in
let le x y = SpecApply ("Le", [x;y]) in
let f, f', r, r' = map4 list_var ("f", "f'", "r", "r'") in
let lenf, lenf', lenr, lenr' = map4 int_var ("lenf", "lenf'", "lenr", "lenr'") in
let vc =
  Implies (And [plus lenr const1 lenr'; cons x r l1; liblazy l1 r';],
           Ite(le lenr' lenf,
               snoc lenf f lenr r x lenf f lenr' r',
               Implies(And[plus lenf lenr' y;reverse r' l2;concat f l2 l3; nil l4; liblazy l4 l5],
                       snoc lenf f lenr r x y l3 const0 l5)
              )
          )
in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Plus" ["x";"y";"z"] [] (int_eq (int_plus x y) z) in
let spec_tab = add_spec spec_tab "Le" ["x";"y"] [] (int_le x y) in
let spec_tab = add_spec spec_tab "Snoc"
    ["lenf";"f";"lenr";"r";"x";"lenf'";"f'";"lenr'";"r'"] ["u"]
    (Implies(Or[member f u; member r u],
             Or[And[member f' u; member r' x]; list_order r' x u; list_order f' u x]
            ))
in
let spec_tab = add_spec spec_tab "Cons" ["h1";"t1";"l1"] ["u"; "v"]
    (E.And [
        (E.Iff (list_order l1 u v,
                    E.Or [E.And [member t1 v; int_eq h1 u]; list_order t1 u v]));
        (head l1 h1);
        E.Implies (member t1 u, member l1 u);
        (* (E.Implies (list_order t1 u v, list_order l1 u v)); *)
        (* (E.Implies (member l1 u,
         *         E.Or [member t1 u; int_eq h1 u])) *)
      ]) in
let spec_tab = add_spec spec_tab "Reverse" ["l1";"l2"] ["u"; "v"]
    (E.And [
        (E.Iff (list_order l1 u v, list_order l2 v u));
        (E.Iff (member l1 u, member l2 u))
      ]) in
let spec_tab = add_spec spec_tab "Concat" ["l1";"l2";"l3"] ["u"; "v"]
    (E.And [
        (E.Iff (E.Or[member l1 u; member l2 u], member l3 u));
        (E.Iff (list_order l3 u v,
                E.Or [E.And [member l1 u; member l2 v];
                      list_order l1 u v; list_order l2 u v]));
      ]) in
let spec_tab = add_spec spec_tab "Lazy" ["l1";"l2"] ["u"; "v"]
    (E.And [
        (E.Iff (list_order l1 u v, list_order l2 u v));
        (E.Iff (member l1 u, member l2 u))
      ]) in
let spec_tab = add_spec spec_tab "Nil" ["l1"] ["u"]
    (E.Not (member l1 u)) in
let axiom = (["l1"; "u"; "v"],
             E.And [
               (* E.Implies (E.And [head l1 u; member l1 v; E.Not (int_eq u v)],
                *            list_order l1 u v); *)
               E.Implies (head l1 u, member l1 u);
               (* E.Implies (list_order l1 u v,
                *            E.And [member l1 u; member l1 v]);
                * E.Implies (E.And [member l1 u; member l1 v; E.Not (int_eq u v)],
                *            E.Or [list_order l1 u v; list_order l1 v u;]); *)
             ]
            ) in
let _ = printf "vc:\n%s\n" (vc_layout vc) in
let ctx =
  Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")] in
let valid, _ = S.check ctx (to_z3 ctx (Not vc) spec_tab) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let valid, _ = S.check ctx
    (Boolean.mk_and ctx [to_z3 ctx (Not vc) spec_tab;
                         E.forallformula_to_z3 ctx axiom
                        ]) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let _ = StrMap.iter (fun name spec ->
    printf "%s\n\n" (layout_spec_entry name spec)) spec_tab in
let _ = printf "axiom:\n%s\n" (E.pretty_layout_forallformula axiom) in
(* let axiom = A.axiom_infer ~ctx:ctx ~vc:vc ~spectable:spec_tab
 *     ~pred_names:["member";"list_order";"==";"head"] ~dttp:E.SE.IntList in
 * let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in *)
();;
