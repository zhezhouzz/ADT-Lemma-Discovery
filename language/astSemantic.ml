module type AstSemantic = sig
  include Ast.Ast
  type value
  val fv: t -> string list
  val type_check : t -> (t * bool)
  val exec: t -> value Utils.StrMap.t -> bool
end

module AstSemantic (A: Ast.Ast)
    (ES: EprSemantic.EprSemantic
           (* with type B.t = A.E.B.t *)
           (* with type t = A.E.t *)
    ):
  AstSemantic with type value = ES.value = struct
  include A
  (* open Utils *)
  type value = ES.value
  let fv _ = []
  let type_check bexpr = (bexpr, true)
  let exec ast _ =
    let rec aux = function
      | Implies (e1, e2) -> if aux e1 then aux e2 else true
      | Ite (e1, e2, e3) -> if aux e1 then aux e2 else aux e3
      | Not e -> not (aux e)
      | And l -> List.for_all (fun x -> x) @@ List.map aux l
      | Or l -> List.exists (fun x -> x) @@ List.map aux l
      | Iff (e1, e2) -> (aux e1) == (aux e2)
      | _ -> true
    in
    aux ast
end
