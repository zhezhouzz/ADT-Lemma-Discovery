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
;;

let assertion ctx vc spec_tab =
  let _ = printf "vc:\n%s\n" (vc_layout vc) in
  let _ = StrMap.iter (fun name spec ->
      printf "%s\n\n" (layout_spec_entry name spec)) spec_tab in
  let axiom = Axiom.infer ~ctx:ctx ~vc:vc ~spectable:spec_tab in
  let axiom = E.forallformula_simplify_ite axiom in
  axiom

let init () =
  let _ = Random.init 0 in
  let ctx =
    Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")] in
  ctx

let spec_tab_add spec_tab {name;intps;outtps;prog} =
  StrMap.add name (Spec.infer ~progtp:(intps,outtps) ~prog:prog) spec_tab

let register spec_tab {name;intps;outtps;prog} =
  let spec_tab = spec_tab_add spec_tab {name;intps;outtps;prog} in
  spec_tab, fun args -> SpecApply (name, args)
