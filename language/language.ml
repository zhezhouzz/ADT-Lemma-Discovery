module Lit = Lit.Lit(LitTree.LitTree)
module SimpleExpr = SimpleExpr.SimpleExpr(SimpleExprTree.SimpleExprTree(Lit))
module Epr = Epr.Epr(EprTree.EprTree(SimpleExpr))
module SpecAst = Ast.Ast(AstTree.AstTree(Epr))

module Helper = struct
  open SpecAst
  open Utils
  module SE = E.SE
  module T = Tp.Tp
  module V = Pred.Value
  type prog = {name:string; intps: T.t list; outtps: T.t list; prog: V.t list -> V.t list}
  let list_var name = SE.Var (T.IntList, name)
  let tree_var name = SE.Var (T.IntTree, name)
  let treei_var name = SE.Var (T.IntTreeI, name)
  let treeb_var name = SE.Var (T.IntTreeB, name)
  let int_var name = SE.Var (T.Int, name)
  let bool_var name = SE.Var (T.Bool, name)
  let add_spec spectab name args fv body =
    StrMap.add name (args, (fv,body)) spectab
  let l0    = list_var "l0"
  let l1    = list_var "l1"
  let l2    = list_var "l2"
  let l3    = list_var "l3"
  let l4    = list_var "l4"
  let l5    = list_var "l5"
  let l6    = list_var "l6"
  let ltmp0    = list_var "ltmp0"
  let t1    = list_var "t1"
  let t2    = list_var "t2"
  let a    = int_var "a"
  let b    = int_var "b"
  let x    = int_var "x"
  let y    = int_var "y"
  let z    = int_var "z"
  let u    = int_var "u"
  let v    = int_var "v"
  let w    = int_var "w"
  let h1    = int_var "h1"
  let h2    = int_var "h2"
  let bool0 = bool_var "bool0"
  let const0 = SE.Literal (T.Int, SE.L.Int 0)
  let const1 = SE.Literal (T.Int, SE.L.Int 1)
  let int_plus a b = SE.Op (T.Int, "+", [a; b])
  let list_member l u = E.Atom (SE.Op (T.Bool, "list_member", [l; u]))
  let tree_member l u = E.Atom (SE.Op (T.Bool, "tree_member", [l; u]))
  let treei_member l u = E.Atom (SE.Op (T.Bool, "treei_member", [l; u]))
  let treeb_member l u = E.Atom (SE.Op (T.Bool, "treeb_member", [l; u]))
  let list_head l u = E.Atom (SE.Op (T.Bool, "list_head", [l; u]))
  let tree_head l u = E.Atom (SE.Op (T.Bool, "tree_head", [l; u]))
  let treei_head l u = E.Atom (SE.Op (T.Bool, "treei_head", [l; u]))
  let treeb_head l u = E.Atom (SE.Op (T.Bool, "treeb_head", [l; u]))
  let list_order l u v = E.Atom (SE.Op (T.Bool, "list_order", [l; u; v]))
  let treel t u v = E.Atom (SE.Op (T.Bool, "tree_left", [t; u; v]))
  let treer t u v = E.Atom (SE.Op (T.Bool, "tree_right", [t; u; v]))
  let treep t u v = E.Atom (SE.Op (T.Bool, "tree_parallel", [t; u; v]))
  let treeil t u v = E.Atom (SE.Op (T.Bool, "treei_left", [t; u; v]))
  let treeir t u v = E.Atom (SE.Op (T.Bool, "treei_right", [t; u; v]))
  let treeip t u v = E.Atom (SE.Op (T.Bool, "treei_parallel", [t; u; v]))
  let treebl t u v = E.Atom (SE.Op (T.Bool, "treeb_left", [t; u; v]))
  let treebr t u v = E.Atom (SE.Op (T.Bool, "treeb_right", [t; u; v]))
  let treebp t u v = E.Atom (SE.Op (T.Bool, "treeb_parallel", [t; u; v]))
  let tree_parent t u v = E.Or [treel t u v; treer t u v]
  let tree_any_order t u v = E.Or [treel t u v; treer t u v; treep t u v]
  let treei_any_order t u v = E.Or [treeil t u v; treeir t u v; treeip t u v]
  let treeb_any_order t u v = E.Or [treebl t u v; treebr t u v; treebp t u v]
  let int_ge a b = E.Atom (SE.Op (T.Bool, ">=", [a;b]))
  let int_le a b = E.Atom (SE.Op (T.Bool, "<=", [a;b]))
  let int_lt a b = E.Atom (SE.Op (T.Bool, "<", [a;b]))
  let int_gt a b = E.Atom (SE.Op (T.Bool, ">", [a;b]))
  let int_eq a b = E.Atom (SE.Op (T.Bool, "==", [a;b]))
  let predefined_spec_tab =
    let spec_tab = StrMap.empty in
    let spec_tab = add_spec spec_tab "plus" ["x";"y";"z"] [] (int_eq (int_plus x y) z) in
    let spec_tab = add_spec spec_tab "le" ["x";"y"] [] (int_le x y) in
    let spec_tab = add_spec spec_tab "equal" ["x";"y"] [] (int_eq x y) in
    spec_tab
end
