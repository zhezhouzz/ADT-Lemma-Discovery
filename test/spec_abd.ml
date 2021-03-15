module Ast = Language.SpecAst
module Value = Pred.Value
module SpecAbd = Inference.SpecAbduction;;

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
let spectable = predefined_spec_tab in
let spectable, cons = register spectable
    {name = "StackPush"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
            prog = function
              | [V.I h; V.L t] -> [V.L (h :: t)]
              | _ -> raise @@ InterExn "bad prog"
    } in
let spectable, is_empty = register spectable
    {name = "IsEmpty"; intps = [T.IntList]; outtps = [T.Bool];
     prog = function
       | [V.L []] -> [V.B false]
       | [V.L _] -> [V.B true]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spectable, stack_head = register spectable
    {name = "StackTop"; intps = [T.IntList]; outtps = [T.Int];
     prog = function
       | [V.L (h :: t)] -> [V.I h]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spectable, stack_tail = register spectable
    {name = "StackTail"; intps = [T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L (h :: t)] -> [V.L t]
       | _ -> raise @@ InterExn "bad prog"
    } in
(* let spectable = add_spec spectable "StackTail" ["l1";"l2"] [] (int_eq l1 l1) in *)
let concat l = SpecApply ("Concat", l) in
let vc =
  Ast.Ite (is_empty [l1],
           concat [l1; l2; l2],
           Implies (And [stack_head [l1; x];
                         stack_tail [l1; l3];
                         concat [l3; l2; l4];
                         cons [x; l4; l5;]],
                    concat [l1; l2; l5])
          )
in
let preds = ["list_once"; "list_member"; "list_order"; "list_head"] in
let bpreds = ["=="] in
let samples = [] in
let hole = "hole" in
let _ = SpecAbd.infer ctx vc spectable hole preds bpreds 1 3 samples in
();;
