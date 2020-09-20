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


(* let _ = printf "List.cross [] [] = (%i)\n" (List.length (List.cross [] [])) in
 * let c = List.combination_l_all [0;2;0;2] in
 * let c = List.remove_duplicates IntList.eq c in
 * let _ = List.iter (fun l -> printf "\t[%s]\n" (IntList.to_string l)) c in *)

let ll = [["a"; "b"];["x"; "x"; "y"];["&"];["@"];["1";"2";"3";"4"]] in
let result = List.choose_list_list ll in
let _ = printf "result:\n";
  List.iter (fun l -> printf "%s\n" (List.to_string (fun x -> x) l)) result in
let ll = [["a"; "b"];["x"; "x"; "y"];["&"];["@"];["1";"2";"3";"4"]] in
let result = List.choose_list_list ([] :: ll) in
let _ = printf "result:\n";
  List.iter (fun l -> printf "%s\n" (List.to_string (fun x -> x) l)) result in
();;
