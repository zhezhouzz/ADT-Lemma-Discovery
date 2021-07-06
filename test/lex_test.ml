let sourcefile = "/Users/zhezhou/workspace/research/ADT-Spec-Inference/data/bench_customstack.ml"
let tool_name = "ocamlc"
let ppf = Format.err_formatter

let parse sourcefile =
  let structure = Pparse.parse_implementation ~tool_name Format.err_formatter sourcefile in
  (* let _ = Printast.structure 0 Format.std_formatter structure in *)
  structure
;;

let _ = Printf.printf "zz:%s\n" (Sys.getcwd ()) in
let structure = parse sourcefile in
let vc = Translate.vcgen structure in
();;
