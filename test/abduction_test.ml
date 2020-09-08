module Ast = Language.Ast.SpecAst;;
open Ast;;
open Printf;;
open Utils;;
module Value = Preds.Pred.Element;;
let module B = E.B in
(* let l0 = B.Var (B.IntList, "l0") in *)
let l1 = B.Var (B.IntList, "l1") in
let l2 = B.Var (B.IntList, "l2") in
let v1 = B.Literal (B.Int, B.L.Int 1) in
let v2 = B.Literal (B.Int, B.L.Int 2) in
let pre = And [SpecApply ("R1", ["l0"; "l1"]); SpecApply ("R2", ["l1"; "l2"])] in
let post_forallfomula =
  [],E.And
    [E.Not (E.Atom (B.Op (B.Bool, "member", [l1; v1])));
     E.Atom (B.Op (B.Bool, "list_order", [l2; v1; v2]))] in
let vc = Implies (pre, SpecApply ("Post", ["l0"; "l1"; "l2"])) in
let _ = printf "vc:\n\t%s\n" @@ layout vc in
let spec_tab = StrMap.empty in
let spec_tab = StrMap.add "Post" (["l0";"l1";"l2"], post_forallfomula) spec_tab in
let _ = printf "where Post:=\n\t%s\n" @@ layout_spec @@ StrMap.find "Post" spec_tab in
let _ = printf "expected result:\n" in
let spec_tab = StrMap.add "R1"
    (["l0"; "l1"], ([], E.Not (E.Atom (B.Op (B.Bool, "member", [l1; v1]))))) spec_tab in
let spec_tab = StrMap.add "R2" (["l1"; "l2"],
    (["u"], E.And
       [E.Atom (B.Op (B.Bool, "list_order", [l2; v1; v2]));
        E.Implies (E.Atom (B.Op (B.Bool, "member", [l1; B.Var (B.Int, "u")])),
                     E.Atom (B.Op (B.Bool, "member", [l2; B.Var (B.Int, "u")])))
       ])) spec_tab in
let _ = printf "R1:=\n\t%s\n" @@ layout_spec @@ StrMap.find "R1" spec_tab in
let _ = printf "R2:=\n\t%s\n" @@ layout_spec @@ StrMap.find "R2" spec_tab in
let value_l0 = Value.L [1;2] in
let value_l1 = Value.L [2] in
let value_l2 = Value.L [2;1;2] in
let env = List.fold_left (fun m (name, v) -> StrMap.add name v m) StrMap.empty
    ["l0", value_l0; "l1", value_l1; "l2", value_l2] in
let _ = printf "eval([1;2],[2],[2;1;2]): %b\n" (exec vc spec_tab env) in
();;

(* negation of vc should be unsat, pre should be satisfiable. *)
