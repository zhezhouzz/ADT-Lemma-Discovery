module Lit = Lit.Lit(LitTree.LitTree)
module SimpleExpr = SimpleExpr.SimpleExpr(SimpleExprTree.SimpleExprTree(Lit))
module Epr = Epr.Epr(EprTree.EprTree(SimpleExpr))
module SpecAst = Ast.Ast(AstTree.AstTree(Epr))

module Helper = struct
  open SpecAst
  open Utils
  module SE = E.SE
  let list_var name = SE.Var (SE.IntList, name)
  let int_var name = SE.Var (SE.Int, name)
  let add_spec spectab name args fv body =
    StrMap.add name (args, (fv,body)) spectab
  let l0    = list_var "l0"
  let l1    = list_var "l1"
  let l2    = list_var "l2"
  let l3    = list_var "l3"
  let l4    = list_var "l4"
  let ltmp0    = list_var "ltmp0"
  let t1    = list_var "t1"
  let t2    = list_var "t2"
  let a    = int_var "a"
  let b    = int_var "b"
  let u    = int_var "u"
  let v    = int_var "v"
  let h1    = int_var "h1"
  let h2    = int_var "h2"
  let const1 = SE.Literal (SE.Int, SE.L.Int 1)
  let int_plus a b = SE.Op (SE.Int, "+", [a; b])
  let member l u = E.Atom (SE.Op (SE.Bool, "member", [l; u]))
  let head l u = E.Atom (SE.Op (SE.Bool, "head", [l; u]))
  let list_order l u v = E.Atom (SE.Op (SE.Bool, "list_order", [l; u; v]))
  let cons h t l = SpecApply ("Cons", [h;t;l])
  let merge_pre l1 l2 l3 = SpecApply ("MergePre", [l1;l2;l3])
  let merge_post l1 l2 l3 = SpecApply ("MergePost", [l1;l2;l3])
  let merge l1 l2 l3 = Implies (merge_pre l1 l2 l3, merge_post l1 l2 l3)
  let int_ge a b = E.Atom (SE.Op (SE.Bool, ">=", [a;b]))
  let int_le a b = E.Atom (SE.Op (SE.Bool, "<=", [a;b]))
  let int_eq a b = E.Atom (SE.Op (SE.Bool, "==", [a;b]))
  let le a b = SpecApply ("Le", [a;b])
end
