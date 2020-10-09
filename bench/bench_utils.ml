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

let get_head dttp =
  match dttp with
  | T.IntList -> "list.dfy.text", "List"
  | T.IntTree -> "tree.dfy.text", "Tree"
  | T.IntTreeI -> "labeled_treei.dfy.text", "LabeledTree"
  | T.IntTreeB -> "labeled_treeb.dfy.text", "LabeledTree"
  | _ -> raise @@ UndefExn "get_head"

let read_whole_file filename =
  let ch = open_in filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let to_verifier name axioms dttp =
  let path = (Sys.getenv "DUNE_ROOT") ^ "/axiom_verifier/" in
  let headfile, dtname = get_head dttp in
  let headfile = path ^ headfile in
  let methods =
    List.fold_left (fun str axiom ->
        sprintf "%sghost method %s<a>(dt: %s<a>, u_0:a, u_1:a)
  ensures %s;{}\n" str (Renaming.unique "axiom") dtname (E.layout (snd axiom))
      ) "" axioms
  in
  let outfile = sprintf "%s%s.dfy" path name in
  let head = read_whole_file headfile in
  let oc = open_out outfile in
  fprintf oc "%s\n%s" head methods;close_out oc

let assertion ctx vc spec_tab =
  (* let _ = printf "vc:\n%s\n" (vc_layout vc) in
   * let _ = StrMap.iter (fun name spec ->
   *     printf "%s\n\n" (layout_spec_entry name spec)) spec_tab in *)
  let axiom = Axiom.infer ~ctx:ctx ~vc:vc ~spectable:spec_tab in
  let axiom = E.forallformula_simplify_ite axiom in
  let _ = printf "axiom:\n\t%s\n" (E.pretty_layout_forallformula axiom) in
  axiom

let init () =
  let _ = Random.init 0 in
  let ctx =
    Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "19999")] in
  ctx

let spec_tab_add spec_tab {name;intps;outtps;prog} =
  StrMap.add name (Spec.infer ~progtp:(intps,outtps) ~prog:prog) spec_tab

let register spec_tab {name;intps;outtps;prog} =
  let spec_tab = spec_tab_add spec_tab {name;intps;outtps;prog} in
  spec_tab, fun args -> SpecApply (name, args)
