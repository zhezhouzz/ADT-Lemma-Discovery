module P = Pred.Pred
module V = Pred.Value
module Ast = Language.SpecAst
module Epr = Ast.E
module SE = Epr.SE
module T = Tp.Tp
module F = Feature.Feature
module FV = Sample.FeatureVector
open Utils
open Z3

type typedvar = T.t * string
type hole = {name: string; args: typedvar list}

type env = {
  qv: typedvar list;
  fset: F.t list;
  pre: Ast.t;
  post: Ast.t;
  spectable: Ast.spec StrMap.t;
  hole: hole;
  applied_args: typedvar list list;
}

let default_spec = [], Epr.True

let rm_hole_from_spectab m hole =
  StrMap.update hole.name (fun v ->
      match v with
      | Some _ -> Some default_spec
      | None -> raise @@ InterExn "rm_hole_from_spectab"
    ) m

let default_constrint = Boolean.mk_true

let multi_apply_constraint ctx env =
  let get_applied_fset args =
    let m = List.fold_left (fun m ((_, name), (_, name')) ->
        StrMap.add name name' m
      ) StrMap.empty (List.combine env.hole.args args)
    in
    List.map (fun f -> F.subst m f) env.fset
  in
  let applied_fset = List.map get_applied_fset env.applied_args in
  match applied_fset with
  | [] -> raise @@ InterExn "never happen in multi_apply_constraint"
  | [_] -> default_constrint ctx
  | fset :: rest ->
    let feature_eq f1 f2 = Epr.Iff (F.to_epr f1, F.to_epr f2) in
    let one fset' =
      Epr.And (List.map (fun (f1, f2) -> feature_eq f1 f2) (List.combine fset fset'))
    in
    let e = Epr.And (List.map one rest) in
    
