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
let testnam = "splayhp" in
let ctx = init () in
let bpreds = ["=="] in
let tr, a1, a2, b1, b2, te = map6 tree_var ("tr", "a1", "a2", "b1", "b2", "te") in
let a, b = map_double tree_var ("a", "b") in
let tr1, tr2, tr3, tr4 = map4 tree_var ("tr1", "tr2", "tr3", "tr4") in
let tree0, tree1, tree2, tree3 = map4 tree_var ("tree0", "tree1", "tree2", "tree3") in
let small, big, nu =
  map_triple tree_var ("small", "big", "nu") in
let x1, x2, y1, y2, pivot = map5 int_var ("x1", "x2", "y1", "y2", "pivot") in
let nu_le1, nu_le2, nu_le3 = map_triple bool_var ("nu_le1", "nu_le2", "nu_le3") in
let nu_e, nu_e2, nu_e3 = map_triple tree_var ("nu_e", "nu_e2", "nu_e3") in
let e, e_hole = make_hole_from_info
    {name = "e"; intps = []; outtps = [T.IntTree;];
     prog = function
       | [] -> Some [V.T Tree.Leaf]
       | _ -> raise @@ InterExn "bad prog"} in
let t, t_hole = make_hole_from_info
    {name = "t"; intps = [T.IntTree;T.Int;T.IntTree;]; outtps = [T.IntTree;];
     prog = function
       | [V.T left; V.I x; V.T right] -> Some [V.T (Tree.Node (x, left, right))]
       | _ -> raise @@ InterExn "bad prog"} in
let partition args =
  Implies (SpecApply ("PartitionPre", args), SpecApply ("PartitionPost", args)) in
let branch1 =
  Ast.make_match [T.IntTree, "b"] [T.IntTree, "tree2"; T.IntTree, "tree3"]
    [
      (Some (e [nu_e]), [(T.IntTree, "nu_e")]),
       (None, [(T.IntTree, "tr"); (T.IntTree, "nu_e")]);
      ((Some (t [b1; y; b2; b]), [(T.IntTree, "b")]),
       (Some
          (Ite(le [y; pivot;nu_le2;],
               And[partition [pivot; b2; small; big];
                   t [a; x; b1; tr1];
                   t [tr1; y; small; tr2];
                   poly_eq [tr2; tree2];
                   poly_eq [big; tree3];
                  ],
               And[partition [pivot; b1; small; big];
                   t [a; x; small; tr1];
                   t [big; y; b2; tr2];
                   poly_eq [tr1; tree2];
                   poly_eq [tr2; tree3];
                  ]
              )),
        [T.IntTree, "tree2"; T.IntTree, "tree3"]
       )
      )
    ]
in
let branch2 =
  Ast.make_match [T.IntTree, "a"] [T.IntTree, "tree2"; T.IntTree, "tree3"]
    [
      (Some (e [nu_e]), [(T.IntTree, "nu_e")]),
      (None, [(T.IntTree, "nu_e"); (T.IntTree, "tr")]);
      (Some (t [a1; y; a2; a]), [T.IntTree, "a";]),
       (Some
          (Ite(le [y; pivot;nu_le3;],
               And[partition [pivot; a2; small; big];
                   t [a1; y; small; tr1];
                   t [big; x; b; tr2];
                   poly_eq [tr1; tree2];
                   poly_eq [tr2; tree3];
                  ],
               And[partition [pivot; a1; small; big];
                   t [a2; x; b; tr1];
                   t [big; y; tr1; tr2];
                   poly_eq [small; tree2];
                   poly_eq [tr2; tree3];
                  ]
              )),
        [T.IntTree, "tree2"; T.IntTree, "tree3"]
       )
    ]
in
let pre =
  Ast.make_match [T.IntTree, "tr"] [T.IntTree, "tree2"; T.IntTree, "tree3"]
    [
      (Some (e [nu_e]), [T.IntTree, "nu_e"]),
       (None, [T.IntTree, "nu_e";T.IntTree, "nu_e"]);
      (Some (t [a; x; b; tr]), [T.IntTree, "tr"]),
      (Some (Ite(le [x; pivot;nu_le1;], branch1, branch2)),
       [T.IntTree, "tree2"; T.IntTree, "tree3"])
       ]
in
let post = partition [pivot; tr; tree2; tree3] in
let elems = [T.Int, "pivot"; T.Int, "x"; T.Int, "y";] in
let holel = [e_hole;
             t_hole
            ] in
let spectable = predefined_spec_tab in
let spectable = set_spec predefined_spec_tab "PartitionPre"
    [T.Int, "x"; T.IntTree, "tr1";T.IntTree, "tr2";T.IntTree, "tr3"] [T.Int, "u"; T.Int, "v"]
    (E.And [
        E.Implies (E.And [treel tr1 u v], int_ge u v);
        E.Implies (E.And [treer tr1 u v], int_le u v);
      ]) in
let spectable = set_spec spectable "PartitionPost"
    [T.Int, "x"; T.IntTree, "tr1";T.IntTree, "tr2";T.IntTree, "tr3"] [T.Int, "u";]
    (
      E.And [
        E.Implies (E.And [tree_member tr2 u], int_le u x);
        E.Implies (E.And [tree_member tr3 u], int_ge u x);
      ]
    )
in
(* let spectable = set_spec spectable "t"
 *     [T.IntTree, "tree0";T.Int, "x";T.IntTree, "tree1";T.IntTree, "tree2"]
 *     [T.Int, "u";T.Int, "v";]
 *     (And [
 *         (\* Iff (tree_head tree2 u, int_eq x u); *\)
 *         Iff (tree_member tree2 u, Or [tree_member tree0 u; tree_member tree1 u; int_eq x u]);
 *         Iff (treel tree2 u v, Or [
 *             treel tree0  u v;
 *             treel tree1 u v;
 *             And [int_eq x u; tree_member tree0 v];
 *           ]);
 *         Iff (treer tree2 u v, Or [
 *             treer tree0 u v;
 *             treer tree1 u v;
 *             And [int_eq x u; tree_member tree1 v];
 *           ]);
 *         (\* Iff (treep tree2 u v, Or [
 *          *     treep tree0 u v;
 *          *     treep tree1 u v;
 *          *     And [treel tree2 x u; treer tree2 x v];
 *          *   ]); *\)
 *       ])
 * in *)
let preds = ["tree_member"; "tree_left"; "tree_right"] in
(* let treelc = Tree.Leaf in
 * let treeh = 3 in
 * let treerc = Tree.(Node(3,Node(1,Node(1,Node(2,Leaf,Leaf),Leaf),Leaf),Leaf)) in
 * let tree3 = Tree.(Node(treeh,treelc, treerc)) in
 * let _ = printf "treel:%s\n" (Tree.layout string_of_int treelc) in
 * let _ = printf "treeh:%s\n" (string_of_int treeh) in
 * let _ = printf "treer:%s\n" (Tree.layout string_of_int treerc) in
 * let _ = printf "tree:%s\n" (Tree.layout string_of_int tree3) in
 * let _ = printf "treerc 3 1 = %b\n" (Tree.left_child (fun x y -> x == y) treerc 3 1) in
 * let _ = printf "tree 3 1 = %b\n" (Tree.left_child (fun x y -> x == y) tree3 3 1) in
 * let _ = raise @@ InterExn "end" in *)
let total_env = SpecAbd.multi_infer
    (sprintf "%s%i" testnam 1) ctx pre post elems spectable holel preds bpreds 2 in
();;
