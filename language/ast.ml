module type Ast = sig
  include AstTree.AstTree
  type value = E.value
  val fv: t -> string list
  val type_check : t -> (t * bool)
  val spec_exec: spec -> string list -> value Utils.StrMap.t -> bool
  val exec: t -> spec Utils.StrMap.t -> value Utils.StrMap.t -> bool
  val spec_to_z3: Z3.context -> string -> spec -> Z3.FuncDecl.func_decl * Z3.Expr.expr
  val to_z3: Z3.context -> t -> spec Utils.StrMap.t -> Z3.Expr.expr
  val neg_to_z3: Z3.context -> t -> spec Utils.StrMap.t -> string list * Z3.Expr.expr
end

module Ast (A: AstTree.AstTree): Ast = struct
  include A
  open Utils
  (* open Printf *)
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
      | ForAll ff -> E.forallformula_exec ff env
      | Implies (e1, e2) -> if aux e1 then aux e2 else true
      | Ite (e1, e2, e3) -> if aux e1 then aux e2 else aux e3
      | Not e -> not (aux e)
      | And l -> List.for_all (fun x -> x) @@ List.map aux l
      | Or l -> List.exists (fun x -> x) @@ List.map aux l
      | Iff (e1, e2) -> (aux e1) == (aux e2)
      | SpecApply (spec_name, args) ->
        let argsvalue = List.map (fun b -> E.B.exec b env) args in
        let args', body = StrMap.find spec_name stable in
        let env = List.fold_left (fun env (k, v) -> StrMap.add k v env) env
            (List.combine args' argsvalue) in
        E.forallformula_exec body env
    in
    aux ast
  open Z3
  open Arithmetic
  open Z3aux
  let spec_to_z3 ctx name (args, forallf) =
    let fdecl = FuncDecl.mk_func_decl_s ctx name
        (List.init (List.length args) (fun _ -> Integer.mk_sort ctx))
        (Boolean.mk_sort ctx) in
    let args = List.map (fun name -> Integer.mk_const_s ctx name) args in
    let body = make_forall ctx args (
        Boolean.mk_iff ctx (FuncDecl.apply fdecl args) (E.forallformula_to_z3 ctx forallf)) in
    fdecl, body

  (* let make_spec_def ctx spec_tab =
   *   StrMap.fold (fun name spec (m, bodys) ->
   *     let fdecl, body = spec_to_z3 ctx name spec in
   *     StrMap.add name fdecl m, body :: bodys
   *   ) spec_tab (StrMap.empty, []) *)
  let to_z3 ctx a spec_tab =
    (* let ptab, bodys = make_spec_def ctx spec_tab in *)
    let rec aux = function
      | ForAll ff -> E.forallformula_to_z3 ctx ff
      | Implies (p1, p2) -> Boolean.mk_implies ctx (aux p1) (aux p2)
      | Ite (p1, p2, p3) -> Boolean.mk_ite ctx (aux p1) (aux p2) (aux p3)
      | Not p -> Boolean.mk_not ctx (aux p)
      | And ps -> Boolean.mk_and ctx (List.map aux ps)
      | Or ps -> Boolean.mk_or ctx (List.map aux ps)
      | Iff (p1, p2) -> Boolean.mk_iff ctx (aux p1) (aux p2)
      | SpecApply (spec_name, argsvalue) ->
        let args, body = StrMap.find spec_name spec_tab in
        E.forallformula_to_z3 ctx @@ E.subst_forallformula body args argsvalue
    in
    aux a
  let neg_to_z3 ctx a spec_tab =
    match a with
    | Implies (p, SpecApply (name, argsvalue)) ->
      let args, body = StrMap.find name spec_tab in
      let body = E.subst_forallformula body args argsvalue in
      let fv, body = E.neg_forallf body in
      fv, to_z3 ctx (And [p;ForAll body]) spec_tab
    | _ -> raise @@ InterExn "neg_to_z3"
end
module Lit = Lit.Lit(LitTree.LitTree)
module Bexpr = Bexpr.Bexpr(BexprTree.BexprTree(Lit))
module Epr = Epr.Epr(EprTree.EprTree(Bexpr))
module SpecAst = Ast(AstTree.AstTree(Epr))
