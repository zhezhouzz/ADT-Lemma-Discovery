open Lexing;;

let sourcefile = "data/bench_customstack.ml" in
let tool_name = "ocamlc" in
let ppf = Format.err_formatter in
let structure = Pparse.parse_implementation ~tool_name ppf sourcefile in
let _ = Printast.structure 0 Format.std_formatter structure in
();;
