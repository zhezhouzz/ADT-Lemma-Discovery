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
  vars: T.tpedvar list
}

type single_result = {
  additional_dt: int D.t;
  additional_spec: Ast.spec;
  init_dt: int D.t;
  init_spec: Ast.spec;
}

type spec_env = {
  current: single_result;
  qv: T.tpedvar list;
  fset: F.t list;
  hole: Language.Helper.hole;
  unknown_fv: T.tpedvar list;
  fvtab: (bool list, D.label) Hashtbl.t
}

type maximal_result =
  | AlreadyMaxed
  | MayAlreadyMaxed
  | NewMaxed of vc * spec_env
  | Weaker of vc * spec_env
