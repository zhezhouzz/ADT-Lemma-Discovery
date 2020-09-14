(**
 * Represents an uninterpreted function application for which we will abduce
 * an interpretation.
 *)

type t = {name: string; params: string list }

let compare_params params1 params2 =
  match List.compare_lengths params1 params2 with
  | 0 ->
     let comp_param c (p1, p2) = if c <> 0 then compare p1 p2 else c in
     List.fold_left comp_param 0 (List.combine params1 params1)
  | c -> c

let compare (abd1: t) (abd2: t) =
  match compare abd1.name abd2.name with
  | 0 -> compare_params abd1.params abd2.params
  | c -> c
