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
let testname = "stream" in
let ctx = init () in
let libcons, libcons_hole = make_hole_from_info
    {name = "Cons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.I h; V.L t] -> Some [V.L (h :: t)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let libnil, libnil_hole = make_hole_from_info
    {name = "Nil"; intps = []; outtps = [T.IntList];
     prog = function
       | [] -> Some [V.L []]
       | _ -> raise @@ InterExn "bad prog"
    } in
let liblazy, liblazy_hole = make_hole_from_info
    {name = "Lazy"; intps = [T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L l] -> Some [V.L l]
       | _ -> raise @@ InterExn "bad prog"
    } in
let libforce, libforce_hole = make_hole_from_info
    {name = "Force"; intps = [T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.L l] -> Some [V.L l]
       | _ -> raise @@ InterExn "bad prog"
    } in
let argl1 = T.IntList, "l1" in
let argl2 = T.IntList, "l2" in
let argnu_l = T.IntList, "nu_l" in
let preds = ["list_member"; "list_head"; "list_order"] in
let bpreds = ["=="] in
let s, acc, tl, nu_cons, nu_lazy, nu_reverse, nu =
  map7 list_var ("s", "acc", "tl", "nu_cons", "nu_lazy", "nu_reverse", "nu") in
let nu_nil, nu_cons2, nu' = map_triple list_var ("nu_nil", "nu_cons2", "nu'") in
let nu_is_empty = bool_var "nu_is_empty" in
let hd = int_var "hd" in
let reverse args = SpecApply ("Reverse", args) in
let pre =
  And [
    make_match [T.IntList, "s"] [T.IntList, "nu"]
      [(Some (And [libnil [nu_nil]; liblazy [nu_nil;s];]), [T.IntList, "s"]),
       (Some (libforce [acc;nu]), [T.IntList, "nu"]);
       (Some (And [libcons [hd;tl;nu_cons]; liblazy [nu_cons;s];]), [T.IntList, "s"]),
       (Some (And [libcons [hd; acc; nu_cons2]; liblazy [nu_cons2; nu_lazy];
                   reverse [nu_lazy; tl; nu_reverse];
                   libforce [nu_reverse; nu]]), [T.IntList, "nu"]);
      ];
    liblazy [nu;nu']
  ]
in
let post = reverse [acc;s;nu'] in
let elems = [T.Int, "hd"] in
(* let vc =
 *   Ast.Ite (is_empty [nu_is_empty; s;],
 *            Implies (liblazy [acc; nu_lazy],
 *                     reverse [acc; s; nu_lazy]
 *                    ),
 *            Implies (And [cons [hd; tl; s];
 *                          cons [hd; acc; nu_cons];
 *                          liblazy [nu_cons; nu_lazy];
 *                          reverse [nu_lazy; tl; nu_reverse];
 *                          libforce [nu_reverse; nu]],
 *                     reverse [acc; s; nu])
 *           )
 * in *)
let holel = [libnil_hole; libcons_hole; liblazy_hole; libforce_hole;] in
let preds = ["list_member";] in
let spectable = add_spec predefined_spec_tab "Reverse"
    [T.IntList, "l1";T.IntList, "l2";T.IntList, "l3"] [T.Int, "u";T.Int, "v"]
    (E.And [
        E.Implies (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
      ])
in
(* let total_env = SpecAbd.multi_infer
 *     (sprintf "%s%i" testname 1) ctx pre post elems spectable holel preds bpreds 1 in *)
let spectable = add_spec predefined_spec_tab "Reverse"
    [T.IntList, "l1";T.IntList, "l2";T.IntList, "l3"] [T.Int, "u";T.Int, "v"]
    (E.And [
        E.Implies (E.Or [list_order l1 u v;
                         list_order l2 v u;
                         E.And [list_member l2 u; list_member l1 v]],
                   list_order l3 u v);
        E.Iff (list_member l3 u, E.Or [list_member l1 u; list_member l2 u]);
      ])
in
let preds = ["list_member"; "list_order"] in
(* let total_env = SpecAbd.multi_infer
 *     (sprintf "%s%i" testname 2) ctx pre post elems spectable holel preds bpreds 2 in *)
let preds = ["list_once"; "list_order"; "list_member"] in
let spec_tab = add_spec predefined_spec_tab "Reverse"
    [T.IntList, "l1";T.IntList, "l2";T.IntList, "l3"] [T.Int, "u";T.Int, "v"; T.Int, "w"]
    (E.And [
        E.Implies (And [list_once l1 v; E.Not (list_member l2 v);
                        list_order l3 u v; list_order l3 v w],
                   list_order l3 u w);
      ])
in
let total_env = SpecAbd.multi_infer
    (sprintf "%s%i" testname 3) ctx pre post elems spectable holel preds bpreds 2 in
();;
