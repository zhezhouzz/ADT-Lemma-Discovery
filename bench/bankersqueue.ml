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
(* let snoc (lenf, f, lenr, r) x =
 *   let lenr = lenr + 1 in
 *   let r = lazy (Cons (x, r)) in
 *   if lenr <= lenf then (lenf, f, lenr, r)
 *   else (lenf + lenr, f ++ reverse r, 0, lazy Nil) *)
let ctx = init () in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Plus" ["x";"y";"z"] [] (int_eq (int_plus x y) z) in
let spec_tab = add_spec spec_tab "Le" ["x";"y"] [] (int_le x y) in
let spec_tab, _ = register spec_tab
    {name = "Cons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.I h; V.L t] -> [V.L (h :: t)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, _ = register spec_tab
    {name = "Nil"; intps = [T.IntList]; outtps = [T.Bool];
     prog = function
       | [V.L []] -> [V.B false]
       | [V.L _] -> [V.B true]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, _ = register spec_tab
    {name = "Lazy"; intps = [T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L l] -> [V.L l]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, _ = register spec_tab
    {name = "Reverse"; intps = [T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L l] -> [V.L (List.rev l)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, _ = register spec_tab
    {name = "Concat"; intps = [T.IntList;T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L l1; V.L l2] -> [V.L (l1 @ l2)]
       | _ -> raise @@ InterExn "bad prog"
    } in
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

let spec_tab = add_spec spec_tab "Snoc"
    ["lenf";"f";"lenr";"r";"x";"lenf'";"f'";"lenr'";"r'"] ["u"]
    (Iff(Or[list_member f u; list_member r u],
         Or[And[list_member f' u; list_member r' x]; list_order r' x u; list_order f' u x]
        ))
in
let axiom = assertion ctx vc spec_tab in
let _ = printf "axiom:\n\t%s\n" (E.pretty_layout_forallformula axiom) in

let spec_tab = add_spec spec_tab "Snoc"
    ["lenf";"f";"lenr";"r";"x";"lenf'";"f'";"lenr'";"r'"] ["u"]
    (Iff(Or[list_member f u; list_member r u; int_eq u x],
         Or[list_member f' u; list_member r' u]
        ))
in
let axiom = assertion ctx vc spec_tab in
let _ = printf "axiom:\n\t%s\n" (E.pretty_layout_forallformula axiom) in
();;
