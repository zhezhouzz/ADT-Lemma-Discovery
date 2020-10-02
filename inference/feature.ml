module type Feature = sig
  type value = Pred.Value.t
  type variable = string
  type t =
    | Pr of Pred.Pred.t * variable list * variable list
    | Eq of variable * variable
  val exec: t -> value Utils.StrMap.t -> bool
  val layout: t -> string
  val to_epr: t -> Language.SpecAst.E.t
  val eq: t -> t -> bool
end

module Feature : Feature = struct
  module E = Language.SpecAst.E
  module SE = E.SE
  module P = Pred.Pred
  module T = Tp.Tp
  module V = Pred.Value

  open Utils
  open Printf
  type value = Pred.Value.t
  type variable = string
  type t =
    | Pr of Pred.Pred.t * variable list * variable list
    | Eq of variable * variable
  let exec feature m =
    let find = StrMap.find "exec_feature" m in
    match feature with
    | Pr (pred, [dt], args) ->
      let dt = find dt in
      let args = List.map find args in
      P.apply (pred, dt, args)
    | Pr (_, _, _) -> raise @@ UndefExn "exec_feature"
    | Eq (a, b) ->
      let a, b = map_double find (a, b) in V.eq a b

  let eq a b =
    match a, b with
    | Pr (pred, dts, args), Pr (pred', dts', args') ->
      (String.equal pred pred') && (StrList.eq dts dts') && (StrList.eq args args')
    | Eq (a, b), Eq (a', b') ->
      (String.equal a a') && (String.equal b b')
    | _ -> false

  let layout = function
    | Pr (pred, dts, args) ->
      sprintf "%s(%s)" (P.layout pred) (StrList.to_string (dts @ args))
    | Eq (a, b) ->
      sprintf "%s = %s" a b
  let to_epr feature =
    let op, args =
      match feature with
      | Pr (pred, [dt], args) ->
        let info = P.find_pred_info_by_name pred in
        let dt = SE.Var(info.P.dttp, dt) in
        let args = List.map (fun x -> SE.Var(T.Int, x)) args in
        pred, dt :: args
      | Pr (_, _, _) -> raise @@ UndefExn "feature::to_epr"
      | Eq (a, b) -> "==", [SE.Var(T.Int, a); SE.Var(T.Int, b)] in
    E.Atom (E.SE.Op (T.Bool, op, args))

end
