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
let testname =  "bankersq" in
let ctx = init () in
let cons, cons_hole = make_hole_from_info
    {name = "BankersqCons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.I h; V.L t] -> Some [V.L (h :: t)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let nil, nil_hole = make_hole_from_info
    {name = "BankersqNil"; intps = []; outtps = [T.IntList];
     prog = function
       | [] -> Some [V.L []]
       | _ -> raise @@ InterExn "bad prog"
    } in
let liblazy, liblazy_hole = make_hole_from_info
    {name = "Lazy"; intps = [T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L l] -> Some (Lazy.force (lazy [V.L l]))
       | _ -> raise @@ InterExn "bad prog"
    } in
let libforce, libforce_hole = make_hole_from_info
    {name = "Force"; intps = [T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L l] -> Some (Lazy.force (lazy [V.L l]))
       | _ -> raise @@ InterExn "bad prog"
    } in
let reverse, reverse_hole= make_hole_from_info
    {name = "BankersqReverse"; intps = [T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L l] -> Some [V.L (List.rev l)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let concat, concat_hole = make_hole_from_info
    {name = "BankersqConcat"; intps = [T.IntList;T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L l1; V.L l2] -> Some [V.L (l1 @ l2)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let f, r, f', r' = map4 list_var ("f", "r", "f'", "r'") in
let lenf, lenr, lenf', lenr' = map4 int_var ("lenf", "lenr", "lenf'", "lenr'") in
let x, lenf1, lenr1 = map_triple int_var ("x", "lenf1", "lenr1") in
let nu_le = bool_var "nu_le" in
let nu_lazy1, nu_reverse, nu_cons, nu_nil, nu_lazy2, f1, r1 =
  map7 list_var ("nu_lazy1", "nu_reverse", "nu_cons", "nu_nil", "nu_lazy2", "f1", "r1") in
(* let f1, r1 = map_double list_var ("f1", "r1") in
 * let x, lenf, lenr, lenf1, lenr1 =
 *   map5 int_var ("x", "lenf", "lenr", "lenf1", "lenr1") in
 * let nu_le = bool_var "nu_le" in *)
let snoc args = SpecApply ("Snoc", args) in
let pre =
  And[
    intadd [lenr;const1;lenr1];
    cons [x; r; nu_cons;];
    liblazy [nu_cons; r1];
    Ast.Ite(le [lenr1; lenf; nu_le;],
            And [poly_eq [lenf;lenf'];
                 libforce [f;f1]; liblazy [f1;f'];
                 poly_eq [lenr;lenr']; poly_eq [r1;r']],
            And[
              intadd [lenf;lenr1;lenf1];reverse [r1;nu_reverse]; concat [f;nu_reverse;f1];
              nil [nu_nil]; liblazy [nu_nil; nu_lazy2];
              poly_eq [lenf1;lenf']; poly_eq [f1;f']; poly_eq [const0;lenr'];
              poly_eq [nu_lazy2;r']
            ]
           )
  ]
in
let client_code lenf f lenr r x =
  let snoc (lenf, f, lenr, r) x =
    let lenr = lenr + 1 in
    let r = x :: r in
    if lenr <= lenf then (lenf, f, lenr, r)
    else (lenf + lenr, f @ (List.rev r), 0, [])
  in
  snoc (lenf, f, lenr, r) x
in
let mii =
  let open SpecAbd in
  {upost = snoc [lenf;f;lenr;r;x;lenf';f';lenr';r'];
   uvars = [T.Int, "x";];
   uinputs = [T.Int, "lenf"; T.IntList, "f";T.Int, "lenr"; T.IntList, "r"; T.Int, "x"];
   uoutputs = [T.Int, "lenf'"; T.IntList, "f'";T.Int, "lenr'"; T.IntList, "r'"];
   uprog = function
     | [V.I lenf; V.L f; V.I lenr; V.L r; V.I x;] ->
       let (lenf', f', lenr', r') = client_code lenf f lenr r x in
       Some [V.I lenf'; V.L f'; V.I lenr'; V.L r';]
     | _ -> raise @@ InterExn "bad prog"
  }
in
(* let vc =
 *   Implies(And[
 *       intadd [lenr;const1;lenr1];
 *       cons [x; r; nu_cons;];
 *       liblazy [nu_cons; r1];
 *     ],
 *           Ast.Ite(le [nu_le; lenr1; lenf],
 *                   snoc [lenf;f;lenr;r;x;lenf;f;lenr1;r1],
 *                   Implies(
 *                     And [intadd [lenf;lenr1;lenf1];
 *                          reverse [r1;nu_reverse];
 *                          concat [f;nu_reverse;f1];
 *                          is_empty [booltrue; lnil];
 *                          liblazy [lnil; nu_lazy2];
 *                         ],
 *                     snoc [lenf;f;lenr;r;x;lenf1;f1;const0;nu_lazy2]
 *                   )
 *                  )
 *     )
 * in *)
let holel = [
  nil_hole;
  cons_hole;
  liblazy_hole;
  libforce_hole;
  concat_hole;
  reverse_hole;] in
let preds = ["list_member";] in
let spectable = add_spec predefined_spec_tab "Snoc"
    [T.Int, "lenf";T.IntList, "f";T.Int, "lenr";T.IntList, "r"; T.Int, "x";
     T.Int, "lenf'";T.IntList, "f'";T.Int, "lenr'";T.IntList, "r'"]
    [T.Int,"u"]
    (E.Iff(Or[list_member f u; list_member r u; int_eq u x],
           Or[list_member f' u; list_member r' u]
          ))
in
(* let total_env = SpecAbd.multi_infer
 *     (sprintf "%s%i" testname 1) ctx mii pre spectable holel preds 1 in *)
let preds = ["list_member"; "list_order"] in
let spectable = add_spec spectable "Snoc"
    [T.Int, "lenf";T.IntList, "f";T.Int, "lenr";T.IntList, "r"; T.Int, "x";
     T.Int, "lenf'";T.IntList, "f'";T.Int, "lenr'";T.IntList, "r'"]
    [T.Int,"u"]
    (Iff(Or[list_member f u; list_member r u],
         Or[And[list_member f' u; list_member r' x]; list_order r' x u; list_order f' u x]
        ))
in
let total_env = SpecAbd.multi_infer
    (sprintf "%s%i" testname 2) ctx mii pre spectable holel preds 1 in
();;
