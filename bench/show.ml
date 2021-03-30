module SpecAbd = Inference.SpecAbduction;;
let bpreds = ["=="] in
let preds = ["list_member"; "list_head"] in
let _ = SpecAbd.merge_max_result "customstk1_maximal.json" preds bpreds in
(* let preds = ["list_member"; "list_head"; "list_order"] in
 * let _ = SpecAbd.merge_max_result "customstk2_maximal.json" preds bpreds in *)
();;
