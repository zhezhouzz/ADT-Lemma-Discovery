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
let testname = "rbset" in
(* let balance = function
 *   | B, Rbset.T (R, Rbset.T (R, a, x, b), y, c), z, d -> Rbset.makeT (R, Rbset.makeT (B, a, x, b), y, Rbset.makeT (B, c, z, d))
 *   | B, Rbset.T (R, Rbset.E, x, Rbset.T (R, b, y, c)), z, d -> Rbset.makeT (R, Rbset.makeT (B, Rbset.E, x, b), y, Rbset.makeT (B, c, z, d))
 *   | B, Rbset.T (R, Rbset.E, x, Rbset.E), z, d -> Rbset.makeT (R, Rbset.makeT (R, Rbset.E, x, Rbset.E), z, d)
 *   | B, Rbset.E, x, Rbset.T (R, Rbset.T (R, b, y, c), z, d) -> Rbset.makeT (R, Rbset.makeT (B, Rbset.E, x, b), y, Rbset.makeT (B, c, z, d))
 *   | B, Rbset.E, x, Rbset.T (R, Rbset.E, y, Rbset.T (R, c, z, d)) -> Rbset.makeT (R, Rbset.makeT (B, Rbset.E, x, Rbset.E), y, Rbset.makeT (B, c, z, d))
 *   | B, Rbset.E, x, Rbset.T (R, Rbset.E, y, Rbset.E) -> Rbset.makeT (R, Rbset.E, x, Rbset.makeT (R, Rbset.E, y, Rbset.E))
 *   | B, Rbset.E, x, Rbset.E -> Rbset.makeT (R, Rbset.E, x, Rbset.E)
 *   | R, b, x, d -> Rbset.makeT (R, b, x, d) *)
let ctx = init () in
let t br l e r result = SpecApply ("RbsetMaketree", [br;l;e;r;result]) in
let e result = SpecApply ("RbsetIsEmpty", [result]) in
let a, b, c, d = map4 treeb_var ("a", "b", "c", "d") in
let tmp1, tmp2, tmp3, tmp4 = map4 treeb_var ("tmp1", "tmp2", "tmp3", "tmp4") in
let tree0, tree1, tree2, tree3 = map4 treeb_var ("tree0", "tree1", "tree2", "tree3") in
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
    {name = "RbsetMaketree"; intps = [T.Bool; T.IntTreeB; T.Int; T.IntTreeB];
     outtps = [T.IntTreeB];
     prog = function
       | [V.B r; V.TB a; V.I x; V.TB b] -> [V.TB (LabeledTree.Node(r,x,a,b))]
       | _ -> raise @@ InterExn "bad prog"
    } in
(* let spec_tab = add_spec spec_tab "RbsetMaketree" ["r1"; "tree0";"x";"tree1";"tree2"] ["u"; "v"]
 *     (And [
 *         Iff (treeb_head tree2 u, int_eq x u);
 *         Iff (treeb_member tree2 u, Or [treebl tree2 x u; treebr tree2 x u; treeb_head tree2 u]);
 *         Iff (treebl tree2 u v, Or [
 *             treebl tree0  u v;
 *             treebl tree1 u v;
 *             And [treeb_head tree2 u; treeb_member tree0 v];
 *           ]);
 *         Iff (treebr tree2 u v, Or [
 *             treebr tree0 u v;
 *             treebr tree1 u v;
 *             And [treeb_head tree2 u; treeb_member tree1 v];
 *           ]);
 *         Iff (treebp tree2 u v, Or [
 *             treebp tree0 u v;
 *             treebp tree1 u v;
 *             And [treebl tree2 x u; treebr tree2 x v];
 *           ]);
 *       ])
 * in *)
let spec_tab, libe = register spec_tab
    {name = "RbsetIsEmpty"; intps = [T.IntTreeB]; outtps = [T.Bool];
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
let preds = ["treeb_head"; "treeb_member"; "treeb_left"; "treeb_right"; "treeb_parallel";
             "treeb_once"
            ] in
let bpreds = ["=="] in
let balance a b c d e = SpecApply ("Balance", [a;b;c;d;e]) in
let _ = print_vc_spec (vc balance) spec_tab in
let spec_tab = add_spec spec_tab "Balance"  ["r1";"tree1";"x";"tree2";"tree3"] ["u"]
    (E.And [
        E.Iff (treeb_member tree3 u,
               E.Or [treeb_member tree1 u; treeb_member tree2 u; int_eq u x]
              );
      ])
in
let _ = printf_assertion spec_tab ["Balance"] in
let axiom1 = assertion ctx (vc balance) spec_tab preds bpreds 350 6 true testname "axiom1" in

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
    (* (E.And [
     *     E.Implies(tree_member tree1 u, tree_once tree1 u);
     *     E.Implies(tree_member tree2 u, tree_once tree2 u);
     *     E.Implies (E.And [treeb_member tree1 u; treeb_member tree1 v],
     *                Not (int_eq u v));
     *     E.Implies (E.Or[treeb_member tree1 u; treeb_member tree2 u], Not (int_eq u x));
     *   ]) *)
in
let spec_tab = add_spec spec_tab "BalancePost" ["r1";"tree1";"x";"tree2";"tree3"] ["u"; "v"]
    (E.And [
        (* tree_once tree3 u; *)
        (* E.Implies(tree_member tree3 u, tree_once tree3 u); *)
        E.Implies (treeb_any_order tree3 u v, Not (int_eq u v));
        E.Iff (treeb_member tree3 u,
               E.Or [treeb_member tree1 u; treeb_member tree2 u; int_eq u x]
              );
      ])
in
let _ = printf_assertion spec_tab ["BalancePre"; "BalancePost"] in
let axiom2 = assertion ctx (vc balance) spec_tab  preds bpreds 400 6 true testname "axiom2" in
let _ = to_verifier testname [axiom1;axiom2] in
();;
