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
let bench_name = "trie" in
let ctx = init () in
let cons, cons_hole = make_hole_from_info
    {name = "cons"; intps = [T.Int; T.IntList]; outtps = [T.IntList];
     prog = function
       | [V.I h; V.L t] -> Some [V.L (h :: t)]
       | _ -> raise @@ InterExn "bad prog"
    } in
let nil, nil_hole = make_hole_from_info
    {name = "nil"; intps = []; outtps = [T.IntList];
     prog = function
       | [] -> Some [V.L []]
       | _ -> raise @@ InterExn "bad prog"
    } in
let t, t_hole = make_hole_from_info
    {name = "triet"; intps = [T.IntTree;T.Int;T.IntTree]; outtps = [T.IntTree];
     prog = function
       | [V.T l; V.I a; V.T r] -> Some [V.T (Tree.Node (a, l, r))]
       | _ -> raise @@ InterExn "bad prog"
    } in
let e, e_hole = make_hole_from_info
    {name = "e"; intps = []; outtps = [T.IntTree;];
     prog = function
       | [] -> Some [V.T Tree.Leaf]
       | _ -> raise @@ InterExn "bad prog"
    } in
let ins args = SpecApply ("Ins", args) in
let nu_nil, i, i' = map_triple list_var ("nu_nil", "i", "i'") in
let m, l, r, nu_e, tmp1, nu = map6 tree_var ("m", "l", "r", "nu_e", "tmp1", "nu") in
let default, a, z, y = map4 int_var ("default", "a", "z", "y") in
let nu_gt = bool_var "nu_gt" in
let branche =
  Ast.make_match [T.IntList, "i";]
    [T.IntList, "nu"]
    [(Some (nil [nu_nil;];),
      [T.IntList, "nu_nil";]),
     (Some (t [nu_e;a;nu_e;nu]),
      [(T.IntTree, "nu");]);
     (Some (cons [z;i';i];),
      [T.IntList, "i";]),
     (Some (
         Ite (gt [z;const0;nu_gt],
              And [ins [default;i';a;nu_e;tmp1];
                   t [tmp1;default;nu_e;nu]],
              And [ins [default;i';a;nu_e;tmp1];
                   t [nu_e;default;tmp1;nu]]
             )
       ),
      [(T.IntList, "nu");]);
    ]
in
let brancht =
  Ast.make_match [T.IntList, "i";]
    [T.IntList, "nu"]
    [(Some (nil [nu_nil;];),
      [T.IntList, "nu_nil";]),
     (Some (t [l;a;r;nu]),
      [(T.IntTree, "nu");]);
     (Some (cons [z;i';i];),
      [T.IntList, "i";]),
     (Some (
         Ite (gt [z;const0;nu_gt],
              And [ins [default;i';a;l;tmp1];
                   t [tmp1;y;r;nu]],
              And [ins [default;i';a;r;tmp1];
                   t [l;y;tmp1;nu]]
             )
       ),
      [(T.IntList, "nu");]);
    ]
in
let pre =
  Ast.make_match [T.IntTree, "m";]
    [T.IntTree, "nu"]
    [(Some (e [nu_e;];), [T.IntTree, "nu_e";]),
     (Some branche, [(T.IntTree, "nu");]);
     (Some (t [l;y;r;m];), [T.IntTree, "m";]),
     (Some brancht, [(T.IntTree, "nu");]);
    ]
in
let client_code default i a m =
  let open Tree in
  let rec ins default i a m =
    match m with
    | Leaf ->
      (match i with
       | [] -> Node(a, Leaf, Leaf)
       | z :: i' ->
         if z > 0
         then Node(default, ins default i' a Leaf, Leaf)
         else Node(default, Leaf, ins default i' a Leaf)
      )
    | Node(y, l, r) ->
      (match i with
       | [] -> Node(a, l, r)
       | z :: i' ->
         if z > 0
         then Node(y, ins default i' a l, r)
         else Node(y, l, ins default i' a r)
      )
  in
  ins default i a m
in
let mii =
  let open SpecAbd in
  {upost = ins [default;i;a;m;nu];
   uvars = [T.Int, "default";T.Int, "a";T.Int, "z";T.Int, "y"];
   uinputs = [T.Int, "default"; T.IntList, "i"; T.Int, "a"; T.IntTree, "m"];
   uoutputs = [T.IntTree, "nu'"];
   uprog = function
     | [V.I default; V.L i; V.I a; V.T m;] -> Some [V.T (client_code default i a m)]
     | _ -> raise @@ InterExn "bad prog"
  }
in
let holel =
  [nil_hole;
   cons_hole;
   e_hole;
   t_hole] in
let which_bench = Array.get Sys.argv 1 in
if String.equal which_bench "1" then
  let preds = ["list_member"; "tree_member";] in
  let spectable = add_spec predefined_spec_tab "Ins"
      [T.Int, "default"; T.IntList, "i"; T.Int, "a"; T.IntTree, "m";T.IntTree, "nu"]
      [T.Int, "u"]
      (E.And [
          E.Implies (tree_member nu u, Or [tree_member m u; int_eq u default; int_eq u a]);
        ])
  in
  let total_env = SpecAbd.multi_infer
      (sprintf "%s%s" bench_name which_bench) ctx mii pre spectable holel preds 1 in
  ()
else raise @@ InterExn "no such bench";;
