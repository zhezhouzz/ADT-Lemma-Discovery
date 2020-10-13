module Ast = Language.SpecAst
module Value = Pred.Value
module S = Solver;;
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
(* let balance = function
 *   | B, T (R, T (R, a, x, b), y, c), z, d -> T (R, T (B, a, x, b), y, T (B, c, z, d))
 *   | B, T (R, E, x, T (R, b, y, c)), z, d -> T (R, T (B, E, x, b), y, T (B, c, z, d))
 *   | B, T (R, E, x, E), z, d -> T (R, T (R, E, x, E), z, d)
 *   | B, E, x, T (R, T (R, b, y, c), z, d) -> T (R, T (B, E, x, b), y, T (B, c, z, d))
 *   | B, E, x, T (R, E, y, T (R, c, z, d)) -> T (R, T (B, E, x, E), y, T (B, c, z, d))
 *   | B, E, x, T (R, E, y, E) -> T (R, E, x, T (R, E, y, E))
 *   | B, E, x, E -> T (R, E, x, E)
 *   | R, b, x, d -> T (R, b, x, d) *)
let ctx = init () in
let t br l e r result = SpecApply ("T", [br;l;e;r;result]) in
let e result = SpecApply ("E", [result]) in
let a, b, c, d = map4 treeb_var ("a", "b", "c", "d") in
let tmp1, tmp2, tmp3, tmp4 = map4 treeb_var ("tmp1", "tmp2", "tmp3", "tmp4") in
let tree1, tree2, tree3 = map_triple treeb_var ("tree1", "tree2", "tree3") in
let tmpe = treeb_var "tmpe" in
let r1, r2= map_double bool_var ("r1", "r2") in
let red r = SpecApply ("R", [r]) in
let black r = SpecApply ("B", [r]) in
let redb r = E.Atom(SE.Op (T.Bool, "==", [r;SE.Literal (T.Bool, SE.L.Bool true)])) in
let blackb r = E.Not(redb r) in
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "R" ["a"] [] (redb a) in
let spec_tab = add_spec spec_tab "B" ["a"] [] (blackb a) in
let spec_tab, libt = register spec_tab
    {name = "T"; intps = [T.Bool; T.IntTreeB; T.Int; T.IntTreeB];
     outtps = [T.IntTreeB];
     prog = function
       | [V.B r; V.TB a; V.I x; V.TB b] -> [V.TB (LabeledTree.Node(r,x,a,b))]
       | _ -> raise @@ InterExn "bad prog"
    } in
let spec_tab, libe = register spec_tab
    {name = "E"; intps = [T.IntTreeB]; outtps = [T.Bool];
     prog = function
       | [V.TB LabeledTree.Leaf] -> [V.B true]
       | [V.TB _] -> [V.B false]
       | _ -> raise @@ InterExn "bad prog"
    } in
let vc balance =
  Implies(And [black r1; red r2; e tmpe;],
          And [
            Implies(And [t r2 a x b tmp1; t r2 tmp1 y c tree1;
                         t r1 a x b tmp2; t r1 c z d tmp3; t r2 tmp2 y tmp3 tmp4;],
                    balance r1 tree1 z d tmp4);
            Implies(And [t r2 b y c tmp1; t r2 tmpe x tmp1 tree1;
                         t r1 tmpe x b tmp2; t r1 c z d tmp3; t r2 tmp2 y tmp3 tmp4;],
                    balance r1 tree1 z d tmp4);
            Implies(And [t r2 tmpe x tmpe tree1;
                         t r2 tree1 z d tmp4;],
                    balance r1 tree1 z d tmp4);
            Implies(And [t r2 b y c tmp1; t r2 tmp1 z d tree2;
                         t r1 tmpe x b tmp2; t r1 c z d tmp3; t r2 tmp2 y tmp3 tmp4;],
                    balance r1 tmpe x tree2 tmp4);
            Implies(And [t r2 c z d tmp1; t r2 tmpe y tmp1 tree2;
                         t r1 tmpe x tmpe tmp2; t r1 c z d tmp3; t r2 tmp2 y tmp3 tmp4;],
                    balance r1 tmpe x tree2 tmp4);
            Implies(And [t r2 tmpe x tmpe tmp4;],
                    balance r1 tmpe x tmpe tmp4);
            Implies(And [t r1 b x d tmp4;],
                    balance r1 b x d tmp4);
          ]
         )
in
let balance a b c d e = SpecApply ("Balance", [a;b;c;d;e]) in
let spec_tab = add_spec spec_tab "Balance"  ["r1";"tree1";"x";"tree2";"tree3"] ["u"]
    (E.And [
        E.Iff (treeb_member tree3 u,
               E.Or [treeb_member tree1 u; treeb_member tree2 u; int_eq u x]
              );
      ])
in
let axiom1 = assertion ctx (vc balance) spec_tab true in

let balance a b c d e =
  Implies (SpecApply ("BalancePre", [a;b;c;d;e]), SpecApply ("BalancePost", [a;b;c;d;e])) in
let spec_tab = add_spec spec_tab "BalancePre" ["r1";"tree1";"x";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        E.Implies (treeb_any_order tree1 u v, Not (int_eq u v));
        E.Implies (treeb_any_order tree2 u v, Not (int_eq u v));
        E.Implies (E.And [treeb_member tree1 u; treeb_member tree1 v],
                   Not (int_eq u v));
        E.Implies (E.Or[treeb_member tree1 u; treeb_member tree2 u], Not (int_eq u x));
      ])
in
let spec_tab = add_spec spec_tab "BalancePost" ["r1";"tree1";"x";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        E.Implies (treeb_any_order tree3 u v, Not (int_eq u v));
        E.Iff (treeb_member tree3 u,
               E.Or [treeb_member tree1 u; treeb_member tree2 u; int_eq u x]
              );
      ])
in
let axiom2 = assertion ctx (vc balance) spec_tab true in
let _ = to_verifier "redblackset" [axiom1;axiom2] in
();;
