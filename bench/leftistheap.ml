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
(* let rec merge tree1 tree2 =
 *   match tree1, tree2 with
 *   | tree1, E -> tree1
 *   | E, tree2 -> tree2
 *   | T (rank1, x, a1, b1), T (rank2, y, a2, b2) ->
 *     if Elem.leq x y then makeT x a1 (merge b1 tree2)
 *     else makeT y a2 (merge tree1 b2) *)
let ctx = init () in
let t rank x a b tr = SpecApply ("T", [rank;x;a;b;tr]) in
let e tr = SpecApply ("E", [tr]) in
let makeT x a b tr = SpecApply ("makeT", [x;a;b;tr]) in
let le a b = SpecApply ("Le", [a;b]) in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Le" ["a";"b"] [] (int_le a b) in
let spec_tab, libt = register spec_tab
    {name = "T"; intps = [T.Int; T.Int; T.IntTreeI; T.IntTreeI]; outtps = [T.IntTreeI];
     prog = function
       | [V.I r; V.I x; V.TI a; V.TI b] -> [V.TI (LabeledTree.Node(r,x,a,b))]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, libmaket = register spec_tab
    {name = "makeT"; intps = [T.Int; T.IntTreeI; T.IntTreeI]; outtps = [T.IntTreeI];
     prog = function
       | [V.I x; V.TI a; V.TI b] ->
         let result =
           LabeledTree.(
             let rank = function Leaf -> 0 | Node (r, _, _ ,_) -> r in
             if rank a >= rank b
             then Node (rank b + 1, x, a, b)
             else Node (rank a + 1, x, b, a)
           )
         in
         [V.TI result]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, libe = register spec_tab
    {name = "E"; intps = [T.IntTreeI]; outtps = [T.Bool];
     prog = function
       | [V.TI LabeledTree.Leaf] -> [V.B true]
       | [V.TI _] -> [V.B false]
       | _ -> raise @@ InterExn "bad prog"
    } in
let rank1 = int_var "rank1" in
let rank2 = int_var "rank2" in
let a1, a2, b1, b2 = map4 treei_var ("a1", "a2", "b1", "b2") in
let tmp, tree1, tree2, tree3 = map4 treei_var ("tmp", "tree1", "tree2", "tree3") in
let vc merge = And [
    Implies (e tree2, merge tree1 tree2 tree1);
    Implies (e tree1, merge tree1 tree2 tree2);
    Implies (
      And [t rank1 x a1 b1 tree1; t rank2 y a2 b2 tree2;
           Ite (le x y,
                And [merge b1 tree2 tmp; makeT x a1 tmp tree3],
                And [merge tree1 b2 tmp; makeT y a2 tmp tree3])],
      merge tree1 tree2 tree3)
  ]
in
let merge tree1 tree2 tree3 = SpecApply ("Merge", [tree1;tree2;tree3]) in
let spec_tab = add_spec spec_tab "Merge"  ["tree1";"tree2";"tree3"] ["u"]
    (E.Iff (treei_member tree3 u, E.Or [treei_member tree1 u; treei_member tree2 u]))
in
let axiom = assertion ctx (vc merge) spec_tab in
let _ = printf "axiom:\n\t%s\n" (E.pretty_layout_forallformula axiom) in

let merge tree1 tree2 tree3 = SpecApply ("Merge", [tree1;tree2;tree3]) in
let spec_tab = add_spec spec_tab "Merge"  ["tree1";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        E.Implies (E.And [treei_head tree3 u;
                          E.Or [treei_head tree1 v; treei_head tree2 v;]], int_le u v);
        (E.Iff (treei_member tree3 u, E.Or [treei_member tree1 u; treei_member tree2 u]));
      ])
in
let axiom = assertion ctx (vc merge) spec_tab in
let _ = printf "axiom:\n\t%s\n" (E.pretty_layout_forallformula axiom) in
();;
