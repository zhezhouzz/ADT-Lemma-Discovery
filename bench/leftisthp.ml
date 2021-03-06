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
 *   | tree1, Leftisthp.E -> tree1
 *   | Leftisthp.E, tree2 -> tree2
 *   | Leftisthp.T (rank1, x, a1, b1), T (rank2, y, a2, b2) ->
 *     if Elem.leq x y then Leftisthp.makeT x a1 (merge b1 tree2)
 *     else Leftisthp.makeT y a2 (merge tree1 b2) *)
let testname = "leftisthp" in
let ctx = init () in
let t rank x a b tr = SpecApply ("LeftisthpT", [rank;x;a;b;tr]) in
let e tr = SpecApply ("LeftisthpIsEmpty", [tr]) in
let makeT x a b tr = SpecApply ("LeftisthpMakeT", [x;a;b;tr]) in
let le a b = SpecApply ("Le", [a;b]) in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "Le" ["a";"b"] [] (int_le a b) in
let spec_tab, libt = register spec_tab
    {name = "LeftisthpT"; intps = [T.Int; T.Int; T.IntTreeI; T.IntTreeI]; outtps = [T.IntTreeI];
     prog = function
       | [V.I r; V.I x; V.TI a; V.TI b] -> [V.TI (LabeledTree.Node(r,x,a,b))]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, libmaket = register spec_tab
    {name = "LeftisthpMakeT"; intps = [T.Int; T.IntTreeI; T.IntTreeI]; outtps = [T.IntTreeI];
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
    {name = "LeftisthpIsEmpty"; intps = [T.IntTreeI]; outtps = [T.Bool];
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
let bpreds = ["=="] in
let _ = print_vc_spec (vc merge) spec_tab in
let spec_tab = add_spec spec_tab "Merge"  ["tree1";"tree2";"tree3"] ["u"]
    (E.Iff (treei_member tree3 u, E.Or [treei_member tree1 u; treei_member tree2 u]))
in
let _ = printf_assertion spec_tab ["Merge"] in
let axiom1 = assertion ctx (vc merge) spec_tab
    ["treei_head"; "treei_member"; "treei_left"; "treei_right"; "treei_parallel";
      "treei_node";]
    bpreds 400 5 true testname "axiom1" in

let merge tree1 tree2 tree3 = SpecApply ("Merge", [tree1;tree2;tree3]) in
let spec_tab = add_spec spec_tab "Merge"  ["tree1";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        E.Implies (E.And [treei_head tree3 u;
                          E.Or [treei_head tree1 v; treei_head tree2 v;]], int_le u v);
        (E.Iff (treei_member tree3 u, E.Or [treei_member tree1 u; treei_member tree2 u]));
      ])
in
let _ = printf_assertion spec_tab ["Merge"] in
let axiom2 = assertion ctx (vc merge) spec_tab
    ["treei_head"; "treei_member"; "treei_left"; "treei_right"; "treei_parallel";]
    bpreds 340 5 true testname "axiom2" in
let _ = to_verifier testname [axiom1;axiom2] in
();;
