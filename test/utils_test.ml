open Utils;;
open Printf;;
(* let test_combination all choose =
 *   let c = List.combination all choose in
 *   let _ = printf "C(%i, %i):\n" all choose in
 *   List.iter (fun l -> printf "\t[%s]\n" (IntList.to_string l)) c
 * in
 * let num_all = 5 in
 * let _ = List.init num_all (fun i -> test_combination num_all i) in
 * let p = List.permutation [1;1;2;3] in
 * let _ = printf "permutation of ([1;1;2;3])(%i):\n" (List.length p) in
 * let _ = List.iter (fun l -> printf "\t[%s]\n" (IntList.to_string l)) p in *)
let _ = printf "List.cross [] [] = (%i)\n" (List.length (List.cross [] [])) in
();;
