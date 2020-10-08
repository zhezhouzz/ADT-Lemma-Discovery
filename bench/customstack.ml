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
(* let rec concat l1 l2 =
 *   if is_empty l1 then l2
 *   else cons (stack_head l1) (concat (stack_tail l1) l2) *)
let ctx = init () in
let spec_tab = StrMap.empty in
let spec_tab, cons = register spec_tab
    {name = "Cons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
            prog = function
              | [V.I h; V.L t] -> [V.L (h :: t)]
              | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, is_empty = register spec_tab
    {name = "IsEmpty"; intps = [T.IntList]; outtps = [T.Bool];
     prog = function
       | [V.L []] -> [V.B false]
       | [V.L _] -> [V.B true]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, stack_head = register spec_tab
    {name = "StackHead"; intps = [T.IntList]; outtps = [T.Int];
     prog = function
       | [V.L (h :: t)] -> [V.I h]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, stack_tail = register spec_tab
    {name = "StackTail"; intps = [T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L (h :: t)] -> [V.L t]
       | _ -> raise @@ InterExn "bad prog"
    } in
let concat l = SpecApply ("Concat", l) in
let vc =
  Ite (is_empty [l1],
       concat [l1; l2; l2],
       Implies (And [stack_head [l1; x];
                     stack_tail [l1; l3];
                     concat [l3; l2; l4];
                     cons [x; l4; l5;]],
                concat [l1; l2; l5])
      )
in
let _ = printf "vc:\n%s\n" (vc_layout vc) in

let spec_tab = add_spec spec_tab "Concat" ["l1";"l2";"l3"] ["u"]
      (E.And [
        E.Iff(list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
      ])
in
let axiom1 = assertion ctx vc spec_tab in

let spec_tab = add_spec spec_tab "Concat" ["l1";"l2";"l3"] ["u";"v"]
     (E.And [
        E.Iff(list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
        E.Implies(E.Or [list_order l1 u v; list_order l2 u v],
                  list_order l3 u v);
      ])
in
let axiom2 = assertion ctx vc spec_tab in

let spec_tab = add_spec spec_tab "Concat" ["l1";"l2";"l3"] ["u"]
     (E.And [
        E.Iff(list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
        E.Implies (list_head l3 u, E.Or [list_head l1 u; list_head l2 u])
      ])
in
let axiom3 = assertion ctx vc spec_tab in
let _ = to_verifier "customstack" [axiom1;axiom2;axiom3] T.IntList in
();;
