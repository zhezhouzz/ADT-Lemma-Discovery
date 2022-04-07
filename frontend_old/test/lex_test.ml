let sourcefile = "/Users/zhezhou/workspace/acidifier-master/test/data/bench_customstack.ml" in
let _ = Printf.printf "zz:%s\n" (Sys.getcwd ()) in
let structure = Frontend.parse sourcefile in
let _ = Printast.structure 0 Format.std_formatter structure in
();;
