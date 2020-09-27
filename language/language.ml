module Lit = Lit.Lit(LitTree.LitTree)
module SimpleExpr = SimpleExpr.SimpleExpr(SimpleExprTree.SimpleExprTree(Lit))
module Epr = Epr.Epr(EprTree.EprTree(SimpleExpr))
module SpecAst = Ast.Ast(AstTree.AstTree(Epr))

module Helper = struct
  open SpecAst
  open Utils
  module SE = E.SE
  let list_var name = SE.Var (SE.IntList, name)
  let tree_var name = SE.Var (SE.IntTree, name)
  let int_var name = SE.Var (SE.Int, name)
  let bool_var name = SE.Var (SE.Bool, name)
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
  let h1    = int_var "h1"
  let h2    = int_var "h2"
  let tree1 = tree_var "tree1"
  let tree2 = tree_var "tree2"
  let tree3 = tree_var "tree3"
  let tree4 = tree_var "tree4"
  let tree5 = tree_var "tree5"
  let const0 = SE.Literal (SE.Int, SE.L.Int 0)
  let const1 = SE.Literal (SE.Int, SE.L.Int 1)
  let int_plus a b = SE.Op (SE.Int, "+", [a; b])
  let member l u = E.Atom (SE.Op (SE.Bool, "member", [l; u]))
  let head l u = E.Atom (SE.Op (SE.Bool, "head", [l; u]))
  let list_order l u v = E.Atom (SE.Op (SE.Bool, "list_order", [l; u; v]))
  let treel t u v = E.Atom (SE.Op (SE.Bool, "tree_left", [t; u; v]))
  let treer t u v = E.Atom (SE.Op (SE.Bool, "tree_right", [t; u; v]))
  let treep t u v = E.Atom (SE.Op (SE.Bool, "tree_parallel", [t; u; v]))
  let tree_parent t u v = E.Or [treel t u v; treer t u v]
  let tree_any_order t u v = E.Or [treel t u v; treer t u v; treep t u v]
  let int_ge a b = E.Atom (SE.Op (SE.Bool, ">=", [a;b]))
  let int_le a b = E.Atom (SE.Op (SE.Bool, "<=", [a;b]))
  let int_lt a b = E.Atom (SE.Op (SE.Bool, "<", [a;b]))
  let int_gt a b = E.Atom (SE.Op (SE.Bool, ">", [a;b]))
  let int_eq a b = E.Atom (SE.Op (SE.Bool, "==", [a;b]))
end
