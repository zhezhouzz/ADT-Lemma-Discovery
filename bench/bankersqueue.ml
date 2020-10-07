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
open Frontend.Fast.Fast;;
;;
(* let snoc (lenf, f, lenr, r) x =
 *   let lenr = lenr + 1 in
 *   let r = lazy (Cons (x, r)) in
 *   if lenr <= lenf then (lenf, f, lenr, r)
 *   else (lenf + lenr, f ++ reverse r, 0, lazy Nil) *)
let ctx = init () in
let spec_tab = predefined_spec_tab in
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
let make_lets l body =
  List.fold_right (fun (names, es) body ->
      Let(names, es, body)
    ) l body
in
let ast =
  ("Snoc", [T.Int, "lenf"; T.IntList, "f"; T.Int, "lenr"; T.IntList, "r"; T.Int, "x";],
   make_lets
     [[T.Int, "const1"], Lit (I 1);
      ([T.Int, "lenr'"], App(T.Int, "Plus", [T.Int, "lenr"; T.Int, "const1"]));
      ([T.IntList, "tmp0"], App(T.IntList, "Cons", [T.Int, "x"; T.IntList, "r"]));
      ([T.IntList, "r'"], App(T.IntList, "Lazy", [T.IntList, "tmp0"]));]
     (Ite(T.Int,
          App(T.Int, "Le", [T.Int, "lenr'"; T.Int, "lenf'"]),
          Var [T.Int, "lenf"; T.IntList, "f"; T.Int, "lenr'"; T.IntList, "r'"],
          make_lets
            [[T.Int, "tmp1"], App(T.Int, "Plus", [T.Int, "lenf"; T.Int, "lenr'"]);
             [T.IntList, "tmp5"], App(T.IntList, "Reverse", [T.IntList, "r'"]);
             [T.IntList, "tmp2"], App(T.IntList, "Concat", [T.IntList, "f"; T.IntList, "tmp5"]);
             [T.Int, "tmp3"], Lit (I 0);
             [T.IntList, "tmp6"], App(T.IntList, "Nil", []);
             [T.IntList, "tmp4"], App(T.IntList, "Lazy", [T.IntList, "tmp6"]);
            ]
            (Var [T.Int, "tmp1"; T.IntList, "tmp2"; T.Int, "tmp3"; T.IntList, "tmp4"])
         ))
  )
in
let vc = func_to_vc [T.Int, "x1"; T.IntList, "x2"; T.Int, "x3"; T.IntList, "x4"] ast in
let f, f', r, r' = map4 list_var ("f", "f'", "r", "r'") in
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