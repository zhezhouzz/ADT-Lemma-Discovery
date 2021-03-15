module type Feature = sig
  type value = Pred.Value.t
  type variable = string
  type t =
    | Pr of Pred.Pred.t * variable list * variable list
    | Base of string * variable * variable
    | Bo of variable
  type set = t list
  val exec: t -> value Utils.StrMap.t -> bool
  val layout: t -> string
  val layout_set: set -> string
  val to_epr: t -> Language.SpecAst.E.t
  val eq: t -> t -> bool
  val get_vars: t -> string list * string list
  val make_set: (Tp.Tp.t * string) list -> set
  val make_set_from_preds: string list -> string list -> (Tp.Tp.t * string) -> (Tp.Tp.t * string) list -> set
  val make_set_from_preds_multidt: string list -> string list -> (Tp.Tp.t * string) list -> set
  val make_target: (Tp.Tp.t * string) -> (Tp.Tp.t * string) list -> set
  val subst:string Utils.StrMap.t -> t -> t
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
    | Base of string * variable * variable
    | Bo of variable
  type set = t list
  let exec feature m =
    let find = StrMap.find "exec_feature" m in
    match feature with
    | Pr (pred, [dt], args) ->
      let dt = find dt in
      let args = List.map find args in
      P.apply (pred, dt, args)
    | Pr (_, _, _) -> raise @@ UndefExn "exec_feature"
    | Base ("==", a, b) ->
      let a, b = map_double find (a, b) in V.eq a b
    | Base (">", a, b) ->
      let a, b = map_double find (a, b) in
      (match a, b with
       | V.I a, V.I b -> a > b
       | _, _ -> raise @@ InterExn "undefined feature"
      )
    | Base (_, _, _) -> raise @@ InterExn "undefined feature"
    | Bo x ->
      (match find x with
       | V.B b -> b
       | _ -> raise @@ InterExn "exec_feature")

  let eq a b =
    match a, b with
    | Pr (pred, dts, args), Pr (pred', dts', args') ->
      (String.equal pred pred') && (StrList.eq dts dts') && (StrList.eq args args')
    | Base (op, a, b), Base (op', a', b') ->
      (String.equal op op') && (String.equal a a') && (String.equal b b')
    | Bo a, Bo a' -> String.equal a a'
    | _ -> false

  let layout = function
    | Pr (pred, dts, args) ->
      sprintf "%s(%s)" (P.layout pred) (StrList.to_string (dts @ args))
    | Base (op, a, b) ->
      sprintf "%s %s %s" a op b
    | Bo x -> x
  let to_epr feature =
      match feature with
      | Pr (pred, [dt], args) ->
        let info = P.find_pred_info_by_name pred in
        let dt = SE.Var(info.P.dttp, dt) in
        let args = List.map (fun x -> SE.Var(T.Int, x)) args in
        E.Atom (E.SE.Op (T.Bool, pred, dt :: args))
      | Pr (_, _, _) -> raise @@ UndefExn "feature::to_epr"
      | Base (op, a, b) ->
        E.Atom (E.SE.Op (T.Bool, op, [SE.Var(T.Int, a); SE.Var(T.Int, b)]))
      | Bo x -> E.Atom (SE.Var (T.Bool, x))

  let get_vars = function
    | Pr (_, dts, args) -> dts, args
    | Base (_, a, b) -> [], [a;b]
    | Bo _ -> [], []

  let make_set_from_preds preds basicpreds (_, dtname) basicnames =
    let _, basicnames = List.split basicnames in
    let make_eq_features elems =
      List.map (fun (a, b) -> Base ("==", a, b)) @@
      List.remove_duplicates (fun (a, b) (a', b') ->
          (a == a' && b = b') || (a == b' && b == a')) @@
      List.filter (fun (a, b) -> a <> b) @@
      List.cross elems elems
    in
    let make_comp_features elems =
      List.map (fun (a, b) -> Base (">", a, b)) @@
      List.remove_duplicates (fun (a, b) (a', b') ->
          (a == a' && b = b')) @@
      List.filter (fun (a, b) -> a <> b) @@
      List.cross elems elems
    in
    let make_pr_features preds dt elems =
      let aux info =
        let args_set = List.combination_l elems info.P.num_int in
        let args_set =
          if info.P.permu then
            List.concat (List.map (fun l -> List.permutation l) args_set)
          else args_set
        in
        List.map (fun args -> Pr (info.P.name, [dt], args)) args_set
      in
      List.fold_left (fun r info -> r @ (aux info)) []
        (List.map P.find_pred_info_by_name preds)
    in
    let pr_features = make_pr_features preds dtname basicnames in
    let eq_features =
      match List.find_opt (fun p -> String.equal p "==") basicpreds with
      | Some _ ->  make_eq_features basicnames
      | None -> []
    in
    let comp_features =
      match List.find_opt (fun p -> String.equal p ">") basicpreds with
      | Some _ ->  make_comp_features basicnames
      | None -> []
    in
    pr_features @ eq_features @ comp_features

  let make_set_from_preds_multidt preds basicpreds variables =
    let bvariables, variables = List.partition
        (fun (tp, _) -> match tp with
           | T.Bool -> true
           | _ -> false) variables in
    let bfeatures = List.map (fun (_, name) -> Bo name) bvariables in
    let dts, basics = List.partition
        (fun (tp, _) -> T.is_dt tp) variables in
    bfeatures @ (
      List.fold_left (fun featureset dt ->
          featureset @ (make_set_from_preds preds basicpreds dt basics)
        ) [] dts
    )

  let make_set vars =
    let variable_split (dts, elems, bs) (tp, name) =
      if T.is_dt tp then (tp, name) :: dts, elems, bs else
        match tp with
        | T.Int -> dts, name :: elems, bs
        | T.Bool -> dts, elems, name :: bs
        | _ -> raise @@ UndefExn "make_set_for_variable"
    in
    let dts, elems, bs = List.fold_left variable_split ([], [], []) vars in
    let bo_feature = match bs with
      | [] -> []
      | [name] -> [Bo name]
      | _ -> raise @@ UndefExn "make_set_for_variable: bo_feature"
    in
    let make_eq_features elems =
      List.map (fun (a, b) -> Base ("==", a, b)) @@
      List.remove_duplicates (fun (a, b) (a', b') ->
          (a == a' && b = b') || (a == b' && b == a')) @@
      List.filter (fun (a, b) -> a <> b) @@
      List.cross elems elems
    in
    let make_pr_features (tp, dt) elems =
      let aux info =
        let args_set = List.combination_l elems info.P.num_int in
        let args_set =
          if info.P.permu then
            List.concat (List.map (fun l -> List.permutation l) args_set)
          else args_set
        in
        List.map (fun args -> Pr (info.P.name, [dt], args)) args_set
      in
      List.fold_left (fun r info -> r @ (aux info)) [] (P.tp_to_preds tp)
    in
    let pr_features = List.fold_left
        (fun r v -> r @ (make_pr_features v elems)) [] dts in
    let eq_features = make_eq_features elems in
    pr_features @ eq_features @ bo_feature

  let layout_set (set: set) =
    List.fold_left (fun r feature -> sprintf "%s [%s]" r (layout feature)) "" set

  let make_target (tp, name) elems =
    let elems = List.map (fun (tp, name) ->
        match tp with
        | T.Int -> name
        | _ -> raise @@ UndefExn "make_target"
      ) elems in
    let aux dtname elems info =
      let args = List.sublist elems (0, info.P.num_int) in
      Pr (info.P.name, [dtname], args)
    in
    if T.is_dt tp then
      List.map (aux name elems) (P.tp_to_preds tp)
    else
      match tp with
      | T.Int ->
        if (List.length elems) == 0 then raise @@ InterExn "make_target"
        else [Base ("==", name, List.nth elems 0)]
      | T.Bool -> [Bo name]
      | _ -> raise @@ UndefExn "make_target"

  let subst m x =
    let find m a = StrMap.find "feature:subst" m a in
    match x with
    | Base (op, a, b) -> Base (op, find m a, find m b)
    | Pr (pred, [dt], args) -> Pr (pred, [find m dt], List.map (find m) args)
    | _ -> raise @@ UndefExn "feature:subst"
end
