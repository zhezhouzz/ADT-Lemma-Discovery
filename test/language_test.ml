module L = Language.Lit.Lit;;
module LS = Language.LitSemantic.LitSemantic(L)(Preds.Pred.Element);;
module B = Language.Bexpr.Bexpr(LS);;
module BS = Language.BexprSemantic.BexprSemantic(B)(Preds.Pred.Predicate)(LS);;
module E = Language.Epr.Epr(BS);;
module ES = Language.EprSemantic.EprSemantic(E)(Preds.Pred.Element)(BS);;
module Ast = Language.Ast.Ast(E);;
module AstS = Language.AstSemantic.AstSemantic(Ast)(ES);;
let _ = print_endline "langauge" in
();;
