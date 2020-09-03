open Utils
open Printf
open Atom
open Z3
open Arithmetic
open Z3aux

let member_fun ctx =
  FuncDecl.mk_func_decl_s ctx "Member" [Integer.mk_sort ctx;Integer.mk_sort ctx]
    (Boolean.mk_sort ctx)

let link_fun ctx =
  FuncDecl.mk_func_decl_s ctx "Link" [Integer.mk_sort ctx;
                                      Integer.mk_sort ctx;Integer.mk_sort ctx;
                                      Integer.mk_sort ctx;Integer.mk_sort ctx]
    (Boolean.mk_sort ctx)

let next_fun ctx =
  FuncDecl.mk_func_decl_s ctx "Next" [Integer.mk_sort ctx;
                                      Integer.mk_sort ctx;Integer.mk_sort ctx;
                                      Integer.mk_sort ctx;Integer.mk_sort ctx]
    (Boolean.mk_sort ctx)

let aop_to_z3 ctx op args =
  match op, args with
  | "+", [a; b] -> Arithmetic.mk_add ctx [a; b]
  | "-", [a; b] -> Arithmetic.mk_sub ctx [a; b]
  | _ -> raise @@ ZZExn "aop_to_z3: undefined"

let var_to_z3 ctx name = Integer.mk_const_s ctx name

let rec aexpr_to_z3 ctx = function
  | AInt i -> int_to_z3 ctx i
  | AVar name -> var_to_z3 ctx name
  | Aop (op, args) -> aop_to_z3 ctx op (List.map (aexpr_to_z3 ctx) args)
  | _ -> raise @@ ZZExn "aexpr_to_z3: undefined"

let bop_to_z3 ctx op args =
  match op, args with
  | "=", [a; b] -> Boolean.mk_eq ctx a b
  | "<>", [a; b] -> Boolean.mk_not ctx @@ Boolean.mk_eq ctx a b
  | ">=", [a; b] -> Arithmetic.mk_ge ctx a b
  | "<=", [a; b] -> Arithmetic.mk_le ctx a b
  | ">", [a; b] -> Arithmetic.mk_gt ctx a b
  | "<", [a; b] -> Arithmetic.mk_lt ctx a b
  | _ -> raise @@ ZZExn "op_to_z3: undefined"

let rec bexpr_to_z3 ctx = function
  | Bop (op, args) -> bop_to_z3 ctx op (List.map (aexpr_to_z3 ctx) args)
	| Member (dt, varname) ->
   let v = var_to_z3 ctx varname in
   let dt = aexpr_to_z3 ctx dt in
   FuncDecl.apply (member_fun ctx) [dt;v]
 | Link (dt, uidx, vidx, u, v) ->
   let uidx = int_to_z3 ctx uidx in
   let vidx = int_to_z3 ctx vidx in
   let u = var_to_z3 ctx u in
   let v = var_to_z3 ctx v in
   let dt = aexpr_to_z3 ctx dt in
   FuncDecl.apply (link_fun ctx) [dt;uidx;vidx;u;v]
 | Next (dt, uidx, vidx, u, v) ->
   let uidx = int_to_z3 ctx uidx in
   let vidx = int_to_z3 ctx vidx in
   let u = var_to_z3 ctx u in
   let v = var_to_z3 ctx v in
   let dt = aexpr_to_z3 ctx dt in
   FuncDecl.apply (next_fun ctx) [dt;uidx;vidx;u;v]

let subst_aexpr name value a =
  let rec aux = function
    | AVar name' -> if String.equal name name' then value else AVar name'
    | Aop (op, args) -> Aop(op, List.map aux args)
    | AInt x -> AInt x
    | _ -> raise @@ ZZExn "undefine subst_aexpr"
  in
  aux a

let subst_bexpr name value b =
  let rec aux = function
    | Bop (op, args) -> Bop(op, List.map (subst_aexpr name value) args)
	  | Member (dt, u) -> Member (subst_aexpr name value dt, u)
    | Link (dt, uidx, vidx, u, v) -> Link (subst_aexpr name value dt, uidx, vidx, u, v)
    | Next (dt, uidx, vidx, u, v) -> Next (subst_aexpr name value dt, uidx, vidx, u, v)
  in
  aux b

let axiom_next_link ctx =
  match map4 (Integer.mk_const_s ctx) ("dt","u","v","w") with
  | (dt, u, v, w) ->
  make_forall ctx [dt;u;v] (
    Boolean.mk_iff ctx
      (FuncDecl.apply (link_fun ctx) [dt;int_to_z3 ctx 0; int_to_z3 ctx 1;u;v])
      (Boolean.mk_or ctx
         [FuncDecl.apply (next_fun ctx) [dt;int_to_z3 ctx 0;int_to_z3 ctx 1;u;v];
          make_exists ctx [w] (
            Boolean.mk_and ctx
              [FuncDecl.apply (next_fun ctx) [dt;int_to_z3 ctx 0;int_to_z3 ctx 1;u;w];
               FuncDecl.apply (link_fun ctx) [dt;int_to_z3 ctx 0;int_to_z3 ctx 1;w;v];
              ]
          )
         ]
      )
  )

let axiom_distinct ctx =
  match map4 (Integer.mk_const_s ctx) ("dt","u","v","w") with
  | (dt, u, v, w) ->
    make_forall ctx [dt] (
    Boolean.mk_implies ctx
      (make_forall ctx [u] (
          Boolean.mk_not ctx
            (FuncDecl.apply (link_fun ctx) [dt;int_to_z3 ctx 0; int_to_z3 ctx 1;u;u];)
        ))
      (make_forall ctx [u;v;w] (
          Boolean.mk_implies ctx
            (Boolean.mk_and ctx [
                FuncDecl.apply (next_fun ctx) [dt;int_to_z3 ctx 0; int_to_z3 ctx 1;u;v];
                FuncDecl.apply (next_fun ctx) [dt;int_to_z3 ctx 0; int_to_z3 ctx 1;u;w]]
            ) (Boolean.mk_eq ctx v w)
        ))
  )
