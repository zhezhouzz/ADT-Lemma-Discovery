module SpecAbd = Inference.SpecAbduction;;
let ctx =
  Z3.mk_context [("model", "true"); ("proof", "false"); ("timeout", "9999")] in
let name = Array.get Sys.argv 1 in
let _ = SpecAbd.merge_max_result ctx name in
();;
