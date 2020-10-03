module Ast = Language.SpecAst;;
open Ast;;
open Printf;;
open Utils;;
module V = Pred.Value;;
(* module A = Axiom.AxiomSyn.Syn;; *)
module SpecSyn = Inference.SpecSyn;;
module T = Tp.Tp;;
let module SE = E.SE in

let progtp = [T.Int; T.IntList], [T.IntList] in
let prog inp = match inp with
  | [V.I h; V.L t] -> [V.L (h :: t)]
  | _ -> raise @@ InterExn "bad prog" in
let spec = SpecSyn.infer ~progtp:progtp ~prog:prog in

let progtp = [T.IntList], [T.IntList] in
let prog inp = match inp with
  | [V.L l] -> [V.L l]
  | _ -> raise @@ InterExn "bad prog" in
let spec = SpecSyn.infer ~progtp:progtp ~prog:prog in

let progtp = [T.IntList], [T.Int] in
let prog inp = match inp with
  | [V.L (h :: t)] -> [V.I h]
  | _ -> raise @@ InterExn "bad prog" in
let spec = SpecSyn.infer ~progtp:progtp ~prog:prog in

let progtp = [], [T.IntList] in
let prog inp = [V.L []] in
let spec = SpecSyn.infer ~progtp:progtp ~prog:prog in

let progtp = [T.IntList], [T.IntList] in
let prog inp = match inp with
  | [V.L (h :: t)] -> [V.L t]
  | _ -> raise @@ InterExn "bad prog" in
let spec = SpecSyn.infer ~progtp:progtp ~prog:prog in
();;
