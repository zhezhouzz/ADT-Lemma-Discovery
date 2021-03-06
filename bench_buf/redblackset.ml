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
let t br l e r result = SpecApply ("T", [br;l;e;r;result]) in
let e result = SpecApply ("E", [result]) in
let balance_pre a b c d e = SpecApply ("BalancePre", [a;b;c;d;e]) in
let balance_post a b c d e = SpecApply ("BalancePost", [a;b;c;d;e]) in
let balance a b c d e =
  balance_post a b c d e
    (* Implies (balance_pre a b c d e, balance_post a b c d e) *)
in
let a, b, c, d = map4 treeb_var ("a", "b", "c", "d") in
let tmp1, tmp2, tmp3, tmp4 = map4 treeb_var ("tmp1", "tmp2", "tmp3", "tmp4") in
let tree1, tree2, tree3 = map_triple treeb_var ("tree1", "tree2", "tree3") in
let tmpe = treeb_var "tmpe" in
let r1, r2= map_double bool_var ("r1", "r2") in
let red r = SpecApply ("R", [r]) in
let black r = SpecApply ("B", [r]) in
let redb r = E.Atom(SE.Op (T.Bool, "==", [r;SE.Literal (T.Bool, SE.L.Bool true)])) in
let blackb r = E.Not(redb r) in
let vc =
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
let spec_tab = StrMap.empty in
let spec_tab = add_spec spec_tab "R" ["a"] [] (redb a) in
let spec_tab = add_spec spec_tab "B" ["a"] [] (blackb a) in
let spec_tab = add_spec spec_tab "BalancePre" ["r1";"tree1";"x";"tree2";"tree3"] ["u"; "v"]
    E.True
    (* (E.And [
     *     E.Implies (tree_any_order tree1 u v, Not (int_eq u v));
     *     E.Implies (tree_any_order tree2 u v, Not (int_eq u v));
     *     E.Implies (E.Or[tree_member tree1 u; tree_member tree2 u], Not (int_eq u x));
     *   ]) *)
in
let spec_tab = add_spec spec_tab "BalancePost" ["r1";"tree1";"x";"tree2";"tree3"] ["u"]
    (E.And [
        (* E.Implies (tree_any_order tree3 u v, Not (int_eq u v)); *)
        E.Iff (treeb_member tree3 u,
               E.Or [treeb_member tree1 u; treeb_member tree2 u; int_eq u x]
               (* E.Or [treeb_member tree1 u; treeb_member tree2 u; treeb_head tree3 u] *)
               (* E.Or [treel tree3 x u; treer tree3 x u; tree_head tree3 u] *)
              );
      ])
in
let libt = {name = "T"; intps = [T.Bool; T.IntTreeB; T.Int; T.IntTreeB];
            outtps = [T.IntTreeB];
            prog = function
              | [V.B r; V.TB a; V.I x; V.TB b] -> [V.TB (LabeledTree.Node(r,x,a,b))]
              | _ -> raise @@ InterExn "bad prog"
           } in
let libe = {name = "E"; intps = [T.IntTreeB]; outtps = [T.Bool];
            prog = function
              | [V.TB LabeledTree.Leaf] -> [V.B true]
              | [V.TB _] -> [V.B false]
              | _ -> raise @@ InterExn "bad prog"
           } in
let spec_tab_add spec_tab {name;intps;outtps;prog} =
  StrMap.add name (Spec.infer ~progtp:(intps,outtps) ~prog:prog) spec_tab in
let spec_tab = List.fold_left spec_tab_add spec_tab [libe;libt] in
(* let spec_tab = add_spec spec_tab "E" ["tree1"] ["u"]
 *     (Not (treei_member tree1 u)) in *)
(* let spec_tab = add_spec spec_tab "T" ["r1";"tree1";"x";"tree2";"tree3"] ["u"; "v"]
 *     (E.And [
 *         E.Iff (treeb_member tree3 u,
 *                    E.Or [treeb_member tree1 u; treeb_member tree2 u; int_eq u x]);
 *        ]) in *)
let axiom = (["tree1"; "u"; "v"],
             E.And [
               E.Implies(
                 E.And [tree_head tree1 u; tree_member tree1 v; Not (int_eq u v)],
                 tree_parent tree1 u v);
               E.Implies(tree_head tree1 u, tree_member tree1 u);
               E.Implies(tree_parent tree1 u v, E.And [tree_member tree1 u; tree_member tree1 v]);
             ]
            ) in
let _ = printf "vc:\n%s\n" (vc_layout vc) in
let ctx =
  Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")] in
let valid, _ = S.check ctx (to_z3 ctx (Not vc) spec_tab) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let valid, m = S.check ctx
    (Boolean.mk_and ctx [to_z3 ctx (Not vc) spec_tab;
                         E.forallformula_to_z3 ctx axiom
                        ]) in
let _ = if valid then printf "valid\n" else printf "not valid\n" in
let _ = StrMap.iter (fun name spec ->
    printf "%s\n\n" (layout_spec_entry name spec)) spec_tab in
let axiom = Axiom.infer ~ctx:ctx ~vc:vc ~spectable:spec_tab ~dttp:T.IntTreeB in
let _ = printf "axiom:\n\t%s\n" (E.layout_forallformula axiom) in
();;
