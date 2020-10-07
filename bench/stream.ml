module Ast = Language.SpecAst
module Value = Pred.Value
module Axiom = Inference.AxiomSyn;;
module Spec = Inference.SpecSyn;;

open Ast
open Utils
open Z3
open Printf
module SE = E.SE
module T = Tp.Tp
module V = Pred.Value
open Language.Helper
open Bench_utils
;;
(* let rec reverse' acc s =
 *   lazy (
 *     match s with
 *     | lazy Nil -> Lazy.force acc
 *     | lazy (Cons (hd, tl)) -> Lazy.force (reverse' (lazy (Cons (hd, acc))) tl)) *)
let ctx = init () in
let spec_tab = StrMap.empty in
let spec_tab, cons = register spec_tab
    {name = "Cons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.I h; V.L t] -> [V.L (h :: t)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, libnil = register spec_tab
    {name = "Nil"; intps = [T.IntList]; outtps = [T.Bool];
     prog = function
       | [V.L []] -> [V.B false]
       | [V.L _] -> [V.B true]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, liblazy = register spec_tab
  {name = "Lazy"; intps = [T.IntList]; outtps = [T.IntList];
   prog = function
     | [V.L l] -> [V.L l]
     | _ -> raise @@ InterExn "bad prog"
  } in
let spec_tab, libforce = register spec_tab
  {name = "Force"; intps = [T.IntList]; outtps = [T.IntList];
   prog = function
     | [V.L l] -> [V.L l]
     | _ -> raise @@ InterExn "bad prog"
  } in
let cons h t l = SpecApply ("Cons", [h;t;l]) in
let nil result = SpecApply ("Nil", [result]) in
let liblazy l1 l2 = SpecApply ("Lazy", [l1;l2]) in
let libforce l1 l2 = SpecApply ("Force", [l1;l2]) in
let hd = int_var "hd" in
let acc, s, tl = map_triple list_var ("acc", "s", "tl") in
let tmp1, tmp2, tmp3, tmp4, tmp5 = map5 list_var ("tmp1", "tmp2", "tmp3", "tmp4", "tmp5") in
let vc reverse =
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

let reverse a b c = SpecApply ("Reverse", [a;b;c]) in

let spec_tab = add_spec spec_tab "Reverse" ["l1";"l2";"l3"] ["u";"v"]
    (E.And [
        E.Iff (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
      ])
in
let axiom = assertion ctx (vc reverse) spec_tab in
let _ = printf "axiom:\n\t%s\n" (E.pretty_layout_forallformula axiom) in

let spec_tab = add_spec spec_tab "Reverse" ["l1";"l2";"l3"] ["u";"v"]
    (E.And [
        E.Implies (E.Or [list_order l1 u v;
                         list_order l2 v u;
                         E.And [list_member l2 u; list_member l1 v]],
                   list_order l3 u v);
        E.Iff (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
      ])
in
let axiom = assertion ctx (vc reverse) spec_tab in
let _ = printf "axiom:\n\t%s\n" (E.pretty_layout_forallformula axiom) in
();;
