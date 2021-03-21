module P = Pred.Pred
module V = Pred.Value
module Ast = Language.SpecAst
module Epr = Ast.E
module SE = Epr.SE
module T = Tp.Tp
module F = Feature.Feature
module FV = Sample.FeatureVector
module D = Dtree.Dtree
open Utils

type flow = {
  pre_flow: Ast.t;
  applied_args_map: (T.tpedvar list list) StrMap.t
}

type vc = {
  multi_pre: flow list;
  post: Ast.t;
  spectable: Ast.spec StrMap.t;
}

type spec_env = {
  cur_dt: int D.t;
  current: Ast.spec;
  qv: T.tpedvar list;
  fset: F.t list;
  hole: Language.Helper.hole;
  unknown_fv: T.tpedvar list;
  fvtab: (bool list, D.label) Hashtbl.t
}
