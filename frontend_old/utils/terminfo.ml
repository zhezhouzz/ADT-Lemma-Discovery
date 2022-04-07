(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Basic interface to the terminfo database *)

(* type status =
 *   | Uninitialised
 *   | Bad_term
 *   | Good_term of int
 * ;;
 * external setup : out_channel -> status = "caml_terminfo_setup";;
 * external backup : int -> unit = "caml_terminfo_backup";;
 * external standout : bool -> unit = "caml_terminfo_standout";;
 * external resume : int -> unit = "caml_terminfo_resume";; *)


open Printf

external isatty : out_channel -> bool = "caml_sys_isatty"
external terminfo_rows: out_channel -> int = "caml_terminfo_rows"

type status =
  | Uninitialised
  | Bad_term
  | Good_term

let setup oc =
  let term = try Sys.getenv "TERM" with Not_found -> "" in
  (* Same heuristics as in Misc.Color.should_enable_color *)
  if term <> "" && term <> "dumb" && isatty oc
  then Good_term
  else Bad_term

let num_lines oc =
  let rows = terminfo_rows oc in
  if rows > 0 then rows else 24
(* 24 is a reasonable default for an ANSI-style terminal *)

let backup oc n =
  if n >= 1 then fprintf oc "\027[%dA%!" n

let resume oc n =
  if n >= 1 then fprintf oc "\027[%dB%!" n

let standout oc b =
  output_string oc (if b then "\027[4m" else "\027[0m"); flush oc
