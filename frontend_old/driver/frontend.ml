let tool_name = "ocamlc"
let ppf = Format.err_formatter

let parse ~sourcefile =
  let structure = Pparse.parse_implementation ~tool_name ppf sourcefile in
  let _ = Printast.structure 0 Format.std_formatter structure in
  structure
;;
