open Epr
open Eprtoz3
open Z3
open Z3aux
open Utils

type prog =
  | Loop of
      {pre: Epr.t; post: Epr.spec; cond: Epr.spec;
       body: context -> Epr.spec -> Expr.expr;
       spec: Epr.spec; iv: Epr.spec;
       dupvars0: (Epr.tp * string) list;
       dupvars1: (Epr.tp * string) list}
  | NoLoop of
      {client: Epr.t; specs: Epr.spec list;}

let verify prog =
  let cfg = [("model", "true");
           ("proof", "false");
           ("timeout", "9999")] in
  let ctx = (Z3.mk_context cfg) in
  let verify_vc vc =
    let _ = Printf.printf "vc: %s\n" (Z3.Expr.to_string vc) in
    match Check.check ctx vc with
    | true, None -> Printf.printf "passed\n"
    | false, None -> Printf.printf "unknown\n"
    | _, Some m ->
      Printf.printf "failed\n"
  in
  match prog with
  | Loop {pre; post; cond; body; spec; iv; dupvars0; dupvars1} ->
    raise @@ ZZExn "undefine verify"
  | NoLoop {client; specs} ->
    let vc = Boolean.mk_and ctx [axiom ctx; to_z3 ctx client specs] in
    verify_vc vc
