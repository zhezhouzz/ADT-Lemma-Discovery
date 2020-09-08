module type Ast = sig
  include AstTree.AstTree
  type value = E.value
  val fv: t -> string list
  val type_check : t -> (t * bool)
  val spec_exec: spec -> string list -> value Utils.StrMap.t -> bool
  val exec: t -> spec Utils.StrMap.t -> value Utils.StrMap.t -> bool
end

module Ast (A: AstTree.AstTree): Ast = struct
  include A
  open Utils
  open Printf
  type value = E.value
  let fv _ = []
  let type_check bexpr = (bexpr, true)
  let spec_exec (args, forallf) args' env =
    let argsmap = List.combine args args' in
    let new_env = List.fold_left (fun m (name, name') ->
        StrMap.add name (StrMap.find name' env) m
      ) StrMap.empty argsmap in
    E.forallformula_exec forallf new_env
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
         | None -> raise @@ InterExn (sprintf "Ast::not such spec(%s)" spec_name)
         | Some spec -> spec_exec spec args env
        )
    in
    aux ast
end
module Lit = Lit.Lit(LitTree.LitTree)
module Bexpr = Bexpr.Bexpr(BexprTree.BexprTree(Lit))
module Epr = Epr.Epr(EprTree.EprTree(Bexpr))
module SpecAst = Ast(AstTree.AstTree(Epr))
