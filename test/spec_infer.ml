module Ast = Language.SpecAst;;
open Ast;;
open Printf;;
open Utils;;
module V = Pred.Value;;
(* module A = Axiom.AxiomSyn.Syn;; *)
module SpecSyn = Inference.SpecSyn;;
module T = Tp.Tp;;
type prog = {intps: T.t list; outtps: T.t list; prog: V.t list -> V.t list};;
let module SE = E.SE in

let spec_infer {intps;outtps;prog} = SpecSyn.infer ~progtp:(intps,outtps) ~prog:prog in
(* let is_empty = {intps = [T.IntList]; outtps = [T.Bool];
 *                 prog = function
 *                   | [V.L []] -> [V.B false]
 *                   | [V.L _] -> [V.B true]
 *                   | _ -> raise @@ InterExn "bad prog"
 *                } in
 * let axiom = spec_infer is_empty in *)
let t = {intps = [T.IntTree;T.Int;T.IntTree]; outtps = [T.IntTree];
                prog = function
                  | [V.T l; V.I a; V.T r] -> [V.T (Tree.Node (a, l, r))]
                  | _ -> raise @@ InterExn "bad prog"
               } in
let axiom = spec_infer t in
let e = {intps = [T.IntTree;]; outtps = [T.Bool];
         prog = function
           | [V.T Tree.Leaf] -> [V.B true]
           | [V.T _] -> [V.B false]
           | _ -> raise @@ InterExn "bad prog"
        } in
let axiom = spec_infer e in

(* let progtp = [T.Int; T.IntList], [T.IntList] in
 * let prog inp = match inp with
 *   | [V.I h; V.L t] -> [V.L (h :: t)]
 *   | _ -> raise @@ InterExn "bad prog" in
 * let spec = SpecSyn.infer ~progtp:progtp ~prog:prog in
 * 
 * let progtp = [T.IntList], [T.IntList] in
 * let prog inp = match inp with
 *   | [V.L l] -> [V.L l]
 *   | _ -> raise @@ InterExn "bad prog" in
 * let spec = SpecSyn.infer ~progtp:progtp ~prog:prog in
 * 
 * let progtp = [T.IntList], [T.Int] in
 * let prog inp = match inp with
 *   | [V.L (h :: t)] -> [V.I h]
 *   | _ -> raise @@ InterExn "bad prog" in
 * let spec = SpecSyn.infer ~progtp:progtp ~prog:prog in
 * 
 * let progtp = [], [T.IntList] in
 * let prog inp = [V.L []] in
 * let spec = SpecSyn.infer ~progtp:progtp ~prog:prog in
 * 
 * let progtp = [T.IntList], [T.IntList] in
 * let prog inp = match inp with
 *   | [V.L (h :: t)] -> [V.L t]
 *   | _ -> raise @@ InterExn "bad prog" in
 * let spec = SpecSyn.infer ~progtp:progtp ~prog:prog in *)
();;
