module SpecAbd = Inference.SpecAbduction;;
let name = Array.get Sys.argv 1 in
let _ = SpecAbd.merge_max_result name in
();;
