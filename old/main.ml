open Verify;;
open Printf;;
open Z3;;
open Epr;;
(* let prog = Bench_reverse.prog in
 * let _ = verify prog in *)
(* let prog = Bench_rotate.prog in
 * let _ = verify prog in *)
let _ = printf "start test:\n" in
(* let _ = printf "pre:\n%s\n" (layout_spec Intro.spec) in *)
let _ = verify Intro.case1_origin in
let _ = verify Intro.case2_origin in
let _ = verify Intro.case1_abduction in
let _ = verify Intro.case2_abduction in
(* let prog = Bench_twice.prog in
 * let _ = verify prog in *)

(* let cfg = [("model", "true");
 *            ("proof", "false");
 *            ("timeout", "9999")] in
 * let ctx = (Z3.mk_context cfg) in *)

(* let _, spec = Bench_insertnodup.spec in
 * let _ = printf "spec:\n%s\n" (Epr.layout spec) in
 * let spec' = EprDnf.todnf spec in
 * let _ = printf "spec':\n%s\n" (EprDnf.layout spec') in
 * let _ = printf "spec':\n%s\n" (Expr.to_string (EprDnf.dnf_to_z3 ctx spec')) in
 * let _ = printf "body':\n%s\n" (Expr.to_string (Bench_insertnodup.body ctx Bench_insertnodup.spec)) in *)

(* let _, body = Bench_reverse.body Bench_reverse.spec in
 * let _ = printf "body:\n%s\n" (Epr.layout body) in
 * let body' = EprDnf.todnf body in
 * let _ = printf "body':\n%s\n" (EprDnf.layout body') in
 * let _ = printf "body':\n%s\n" (Expr.to_string (EprDnf.dnf_to_z3 ctx body')) in *)

(* let _, post = Bench_twice.post in
 * let _ = printf "post:\n%s\n" (Epr.layout post) in
 * let post' = EprDnf.todnf post in
 * let _ = printf "post':\n%s\n" (EprDnf.layout post') in
 * let _ = printf "post':\n%s\n" (Expr.to_string (EprDnf.dnf_to_z3 ctx post')) in *)
();;
