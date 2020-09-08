module type AstSemantic = sig
  include Ast.Ast
  module ES: EprSemantic.EprSemantic
    with type B.L.t = E.B.L.t
    with type B.tp = E.B.tp
    with type B.t = E.B.t
    with type t = E.t
  type value = ES.value
  val fv: t -> string list
  val type_check : t -> (t * bool)
  val exec: t -> spec_table -> value Utils.StrMap.t -> bool
end

module AstSemantic (A: Ast.Ast)
    (ES: EprSemantic.EprSemantic
     with type B.L.t = A.E.B.L.t
     with type B.tp = A.E.B.tp
     with type B.t = A.E.B.t
     with type t = A.E.t
    ):
  AstSemantic = struct
  module ES = ES
  include A
  open Utils
  type value = ES.value
  let fv _ = []
  let type_check bexpr = (bexpr, true)
  let exec ast stable env =
    let rec aux = function
      | Implies (e1, e2) -> if aux e1 then aux e2 else true
      | Ite (e1, e2, e3) -> if aux e1 then aux e2 else aux e3
      | Not e -> not (aux e)
      | And l -> List.for_all (fun x -> x) @@ List.map aux l
      | Or l -> List.exists (fun x -> x) @@ List.map aux l
      | Iff (e1, e2) -> (aux e1) == (aux e2)
      | SpecApply (spec_name, args) ->
        (match StrMap.find_opt spec_name stable with
         | None -> raise @@ InterExn "AstSemantic::not such spec"
         | Some (fv, forallf) ->
           let fvmap = List.combine fv args in
           let new_env = List.fold_left (fun m (name, name') ->
               StrMap.add name (StrMap.find name' env) m
             ) StrMap.empty fvmap in
           ES.spec_exec forallf new_env
        )
    in
    aux ast
end
