module Ast = Language.SpecAst
module Value = Preds.Pred.Value
module S = Solver;;
module A = Axiom.AxiomSyn.Syn;;

open Utils
open Z3
open Printf
open Language.Helper;;
open Ast
module SE = E.SE
;;
(* let rec reverse' acc s =
 *   lazy (
 *     match s with
 *     | lazy Nil -> Lazy.force acc
 *     | lazy (Cons (hd, tl)) -> Lazy.force (reverse' (lazy (Cons (hd, acc))) tl)) *)
let cons h t l = SpecApply ("Cons", [h;t;l]) in
let nil result = SpecApply ("Nil", [result]) in
let liblazy l1 l2 = SpecApply ("Lazy", [l1;l2]) in
let libforce l1 l2 = SpecApply ("Force", [l1;l2]) in
let reverse_pre a b c = SpecApply ("ReversePre", [a;b;c]) in
let reverse_post a b c = SpecApply ("ReversePost", [a;b;c]) in
let reverse a b c = Implies (reverse_pre a b c, reverse_post a b c) in
let hd = int_var "hd" in
let acc, s, tl = map_triple list_var ("acc", "s", "tl") in
let tmp1, tmp2, tmp3, tmp4, tmp5 = map5 list_var ("tmp1", "tmp2", "tmp3", "tmp4", "tmp5") in
let vc =
  And [
    Implies(
      And [nil tmp1; liblazy tmp1 s; libforce acc tmp3; liblazy tmp3 l3],
      reverse acc s l3);
    Implies(
      And [cons hd tl tmp1; liblazy tmp1 s; cons hd acc tmp2; liblazy tmp2 tmp3;
           reverse tmp3 tl tmp4; libforce tmp4 tmp5; liblazy tmp5 l3],
      reverse acc s l3);
  ]
in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "ReversePre" ["l1";"l2";"l3"] ["u"; "v"] E.True
in
let spec_tab = add_spec spec_tab "ReversePost" ["l1";"l2";"l3"] ["u";"v"]
    (E.And [
        E.Implies (E.Or [list_order l1 u v;
                         list_order l2 v u;
                         E.And [member l2 u; member l1 v]],
                   list_order l3 u v);
        E.Iff (member l3 u, E.Or [member l1 u; member l2 u]);
      ])
in
let spec_tab = add_spec spec_tab "Nil" ["l1"] ["u";"v"]
    (E.And [
        (Not (member l1 u));
        (Not (list_order l1 u v));
      ])
    in
let spec_tab = add_spec spec_tab "Cons" ["h1";"t1";"l1"] ["u"; "v"]
    (E.And [
        (E.Iff (list_order l1 u v,
                    E.Or [E.And [member t1 v; head l1 u]; list_order t1 u v]));
        (E.Iff (member l1 u, E.Or [member t1 u; int_eq h1 u]));
        head l1 h1;
      ]) in
let spec_tab = add_spec spec_tab "Lazy" ["l1"; "l2"] ["u";"v"]
    (E.And [
        (E.Iff (list_order l1 u v, list_order l2 u v));
        (E.Iff (member l1 u, member l2 u));
      ]) in
let spec_tab = add_spec spec_tab "Force" ["l1"; "l2"] ["u";"v"]
    (E.And [
        (E.Iff (list_order l1 u v, list_order l2 u v));
        (E.Iff (member l1 u, member l2 u));
      ]) in
let axiom = (["l1"; "u"; "v"],
             E.And [
               E.Implies (head l1 u, member l1 u);
               E.Implies (And[head l1 u; head l1 v], int_eq u v);
               E.Implies (list_order l1 u v,
                          E.And [member l1 u; member l1 v]);
             ]
            ) in
let _ = printf "vc:\n%s\n" (vc_layout vc) in
let ctx =
  Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")] in
let valid, _ = S.check ctx (to_z3 ctx (Not vc) spec_tab) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let valid, m = S.check ctx
    (Boolean.mk_and ctx [to_z3 ctx (Not vc) spec_tab;
                         E.forallformula_to_z3 ctx axiom
                        ]) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let _ = match m with
  | None -> printf "none.\n"
  | Some m -> printf "model:\n%s\n" (Model.to_string m) in
(* let _ = StrMap.iter (fun name spec ->
 *     printf "%s\n\n" (layout_spec_entry name spec)) spec_tab in
 * let _ = printf "axiom:\n%s\n" (E.pretty_layout_forallformula axiom) in *)
(* let axiom = A.axiom_infer ~ctx:ctx ~vc:vc ~spectable:spec_tab
 *     ~pred_names:["member";"tree_left";"tree_right";"==";"head"] ~dttp:E.SE.IntTree in
 * let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in *)
();;
