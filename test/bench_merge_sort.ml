module Ast = Language.Ast.SpecAst
module Value = Preds.Pred.Value
module S = Solver;;
module A = Axiom.AxiomSyn.Syn;;

open Ast
open Utils
open Z3
open Z3.Arithmetic
open Printf
module SE = E.SE
;;
(* Some simple literals to aid in test construction. *)
let libcode_cons a l = a :: l in
let rec libmerge l1 l2 =
  match l1, l2 with
  | [], l2 -> l2
  | l1, [] -> l1
  | h1 :: t1, h2 :: t2 ->
    if h1 <= h2
    then h1 :: (libmerge t1 l2)
    else h2 :: (libmerge l1 t2)
in
let clientcode inps =
  match inps with
  | [Value.I h1; Value.I h2; Value.L t1; Value.L t2] ->
    let l1 = libcode_cons h1 t1 in
    let l2 = libcode_cons h2 t2 in
    let ltmp0, l3 =
      if h1 <= h2
      then
        let ltmp0 = libmerge t1 l2 in
        let l3 = libcode_cons h1 ltmp0 in
        ltmp0, l3
      else
        let ltmp0 = libmerge l1 t2 in
        let l3 = libcode_cons h2 ltmp0 in
        ltmp0, l3
    in
    ["h1", Value.I h1; "h2", Value.I h2;
     "t1", Value.L t1; "t2", Value.L t2;
     "l1", Value.L l1; "l2", Value.L l2;
     "ltmp0", Value.L ltmp0; "l3", Value.L l3]
  | _ -> raise @@ TestFailedException "bad clientcode"
in
let list_var name = SE.Var (SE.IntList, name) in
let int_var name = SE.Var (SE.Int, name) in
let add_spec spectab name args fv body =
  StrMap.add name (args, (fv,body)) spectab in
let l1    = list_var "l1" in
let l2    = list_var "l2" in
let l3    = list_var "l3" in
let ltmp0    = list_var "ltmp0" in
let t1    = list_var "t1" in
let t2    = list_var "t2" in
let a    = int_var "a" in
let b    = int_var "b" in
let u    = int_var "u" in
let v    = int_var "v" in
let w    = int_var "w" in
let h1    = int_var "h1" in
let h2    = int_var "h2" in
let member l u = E.Atom (SE.Op (SE.Bool, "member", [l; u])) in
let head l u = E.Atom (SE.Op (SE.Bool, "head", [l; u])) in
let list_order l u v = E.Atom (SE.Op (SE.Bool, "list_order", [l; u; v])) in
let cons h t l = SpecApply ("Cons", [h;t;l]) in
let merge_pre l1 l2 l3 = SpecApply ("MergePre", [l1;l2;l3]) in
let merge_post l1 l2 l3 = SpecApply ("MergePost", [l1;l2;l3]) in
let merge l1 l2 l3 = Implies (merge_pre l1 l2 l3, merge_post l1 l2 l3) in
let int_le a b = E.Atom (SE.Op (SE.Bool, "<=", [a;b])) in
let int_eq a b = E.Atom (SE.Op (SE.Bool, "==", [a;b])) in
let le a b = SpecApply ("Le", [a;b]) in
let vc = Implies (
    And [cons h1 t1 l1; cons h2 t2 l2;
         Ite (le h1 h2,
              And [merge t1 l2 ltmp0; cons h1 ltmp0 l3],
              And [merge l1 t2 ltmp0; cons h2 ltmp0 l3])],
    merge l1 l2 l3) in
let _ = printf "vc:%s\n" (layout vc) in
let vc_nnf = to_nnf (Not vc) in
let _ = printf "vc_nnf:%s\n" (layout vc_nnf) in
let vc_nnf = remove_unsat_clause vc_nnf in
let _ = printf "vc_nnf:%s\n" (layout vc_nnf) in
let vc_dnf = to_dnf vc_nnf in
let _ = match vc_dnf with
  | Or ps -> List.iter (fun p -> printf "%s\n" (layout p)) ps
  | _ -> raise @@ TestFailedException "zz" in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Le" ["a";"b"] [] (int_le a b) in
let spec_tab = add_spec spec_tab "MergePre" ["l1";"l2";"l3"] ["u";"v"]
    (E.And [
        E.Implies (list_order l1 u v, int_le u v);
        E.Implies (list_order l2 u v, int_le u v);
      ]) in
let spec_tab = add_spec spec_tab "MergePost" ["l1";"l2";"l3"] ["u";"v"]
    (E.And [E.Implies (list_order l3 u v, int_le u v);
            E.Implies (member l3 u, E.Or [member l1 u; member l2 u]);
            (* E.Iff (head l3 u, E.Or [head l1 u; head l2 u]); *)
           ])
in
let spec_tab = add_spec spec_tab "Cons" ["h1";"t1";"l1"] ["u"; "v"]
    (E.And [
        (E.Implies (list_order l1 u v,
                    E.Or [E.And [member t1 v; int_eq h1 u]; list_order t1 u v]));
        (head l1 h1);
        (E.Implies (list_order t1 u v, list_order l1 u v));
        (E.Iff (member l1 u,
                E.Or [member t1 u; int_eq h1 u]))
      ]) in
let axiom = (["l1"; "u"; "v"; "w"],
             E.And [
               (* E.Implies (head l1 u, member l1 u); *)
               (* E.Implies (list_order l1 u v, E.And [member l1 u; member l1 v;]); *)
               (* E.Implies (E.And [member l1 u; member l1 v; E.Not (int_eq u v)],
                *            E.Or [list_order l1 u v; list_order l1 v u]); *)
               E.Implies (E.And [head l1 u; member l1 v; E.Not (int_eq u v)],
                          list_order l1 u v);
               (* E.Implies (E.And [head l1 w; list_order l1 u v], list_order l1 w v); *)
             ]
            ) in
let ctx =
  Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")] in
let valid, m = S.check ctx (to_z3 ctx vc_dnf spec_tab) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let valid, m = S.check ctx
    (Boolean.mk_and ctx [to_z3 ctx vc_dnf spec_tab;
                         E.forallformula_to_z3 ctx axiom
                        ]) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
(* let _ = raise @@ TestFailedException "zz" in *)
let axiom = A.axiom_infer ~ctx:ctx ~vc:vc ~spectable:spec_tab ~prog:clientcode in
let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in
let _ = raise @@ TestFailedException "zz" in
let vcz3 = (Boolean.mk_not ctx (to_z3 ctx vc spec_tab)) in
let valid, m = S.check ctx vcz3 in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let _ = match m with
  | None -> printf "none.\n"
  | Some m -> printf "Model: \n%s\n" (Model.to_string m) in
let _ = raise @@ TestFailedException "zz" in
let valid, m = S.check ctx
    (Boolean.mk_and ctx [
        (E.forallformula_to_z3 ctx axiom);
        (Boolean.mk_not ctx (to_z3 ctx vc spec_tab));
      ]
    ) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
();;
