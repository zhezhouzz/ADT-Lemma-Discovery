module type BexprSemantic = sig
  include Bexpr.Bexpr
  module LS: LitSemantic.LitSemantic with type t = L.t
  type value = LS.value
  val fv: t -> string list
  val type_check : t -> (t * bool)
  val exec: t -> value Utils.StrMap.t -> bool
  val extract_dt: t -> value list * string list
end

module BexprSemantic (B: Bexpr.Bexpr)
    (LS: LitSemantic.LitSemantic with type t = B.L.t)
    (P: Preds.Pred.Pred with type E.t = LS.E.t):
  BexprSemantic
  with type LS.E.t = LS.E.t = struct
  include B
  module LS = LS
  open Utils
  type value = LS.value
  let fv _ = []
  let type_check bexpr = (bexpr, true)
  let non_dt_op op args =
    match op, args with
    | "+", [P.E.I a; P.E.I b] -> Some (P.E.I (a + b))
    | "-", [P.E.I a; P.E.I b] -> Some (P.E.I (a - b))
    | "==", [P.E.I a; P.E.I b] -> Some (P.E.B (a == b))
    | "<>", [P.E.I a; P.E.I b] -> Some (P.E.B (a <> b))
    | ">=", [P.E.I a; P.E.I b] -> Some (P.E.B (a >= b))
    | "<=", [P.E.I a; P.E.I b] -> Some (P.E.B (a <= b))
    | ">", [P.E.I a; P.E.I b] -> Some (P.E.B (a > b))
    | "<", [P.E.I a; P.E.I b] -> Some (P.E.B (a < b))
    | _, _ -> None
  let exec bexpr env =
    let rec aux = function
      | Literal (_, lit) -> LS.exec lit
      | Var (_, name) ->
        (match StrMap.find_opt name env with
         | None -> raise @@ InterExn "BexprSemantic::exec"
         | Some v -> v
        )
      | Op (_, op, args) ->
        let args = List.map aux args in
        (match non_dt_op op args with
         | Some v -> v
         | None -> match args with
           | [] -> raise @@ InterExn "BexprSemantic::exec"
           | dt :: args -> P.E.B (P.apply (op, dt, args))
        )
    in
    match aux bexpr with
    | P.E.B b -> b
    | _ -> raise @@ InterExn "BexprSemantic::exec not a bool result"
  let extract_dt bexpr =
    let rec aux = function
      | Literal (_, L.IntList lit) -> [P.E.L lit]
      | Literal (_, L.IntTree lit) -> [P.E.T lit]
      | Op (_, _, args) -> List.concat @@ List.map aux args
      | _ -> []
    in
    let consts = remove_duplicates P.E.eq (aux bexpr) in
    let rec aux = function
      | Var (IntList, name) | Var (IntTree, name) -> [name]
      | Op (_, _, args) -> List.concat @@ List.map aux args
      | _ -> []
    in
    let vars = remove_duplicates String.equal (aux bexpr) in
    consts, vars
end
