module Fast = struct
  type tp = Tp.Tp.t
  type var = tp * string
  type lit = I of int | B of bool
  type t =
    | Var of var list
    | App of (tp * string * var list)
    | Let of (var list * t * t)
    | Ite of (tp * t * t *t)
    | Lit of lit
    | Match of (tp * var list * (t*t) list)
  type op =
    | Add | Minus | Equal | Le | Ge | Lt | Gt
  type func = string * ((Tp.Tp.t * string) list) * t
  open Utils
  module T = Tp.Tp
  module A = Language.SpecAst
  module SE = A.E.SE
  let to_se (tp, name) = SE.Var (tp, name)
  let make_apply name inps outs =
    let inps = List.map to_se inps in
    let outs = List.map to_se outs in
    A.SpecApply (name, inps @ outs)
  let to_vc_body outs ast =
    let rec aux names = function
      | Var names' ->
        A.And (
          List.map (fun (var1, var2) ->
              make_apply "equal" [var1] [var2]
            ) (List.combine names names'))
      | Let (outs, e1, e2) ->
        let formula = aux outs e1 in
        A.And [formula; aux names e2]
      | Ite (_, App (_, fname, args), e2, e3) ->
        A.Ite(A.SpecApply (fname, List.map to_se args),
              aux names e2,
              aux names e3)
      | Ite (_, _, _, _) -> raise @@ UndefExn "to_spec"
      | Lit a ->
        (match a, names with
         | I i, [name] ->
           A.SpecApply ("equal", [to_se name; SE.Literal (T.Int, SE.L.Int i)])
         | B b, [name] ->
           A.SpecApply ("equal", [to_se name; SE.Literal (T.Bool, SE.L.Bool b)])
         | _ , _ -> raise @@ UndefExn "to_spec")
      | Match (_, outs, branchs) ->
        A.And (
          List.map (fun (e, body) ->
              aux names (Let (outs, e, body))
            ) branchs)
      | App (_, name, args) ->
        make_apply name args names
    in
    aux outs ast
  let func_to_vc outs (fname, args, body) =
    A.Implies (to_vc_body outs body, make_apply fname args outs)
end
