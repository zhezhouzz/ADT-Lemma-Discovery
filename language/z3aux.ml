open Z3
open Z3.Expr
open Z3.Boolean
open Z3.Arithmetic

let int_to_z3 ctx i = mk_numeral_int ctx i (Integer.mk_sort ctx)
let bool_to_z3 ctx b = if b then mk_true ctx else mk_false ctx

let arrname_arr arrname = arrname ^ "_a"
let arrname_length arrname = arrname ^ "_length"

let arrii_to_z3 ctx name =
  Z3Array.mk_const_s ctx (arrname_arr name) (Integer.mk_sort ctx) (Integer.mk_sort ctx)

let array_head_ ctx (arrname, idx) =
  let a_length = Integer.mk_const_s ctx (arrname_length arrname) in
  [mk_lt ctx idx a_length; mk_le ctx (int_to_z3 ctx 0) idx]

let array_head ctx (arrname, idxname) =
  let idx = Integer.mk_const_s ctx idxname in
  array_head_ ctx (arrname, idx)

let make_forall ctx forallvars body =
  if List.length forallvars == 0 then body else
    Quantifier.expr_of_quantifier
    (Quantifier.mk_forall_const ctx forallvars
       body
       (Some 1)
       [] [] None None)

let make_exists ctx forallvars body =
  if List.length forallvars == 0 then body else
    Quantifier.expr_of_quantifier
      (Quantifier.mk_exists_const ctx forallvars
         body
         (Some 1)
         [] [] None None)

let quanti_head ctx forallvars existsvars body =
  let p =
    if (List.length existsvars) == 0
    then body
    else
      Quantifier.expr_of_quantifier
        (Quantifier.mk_exists_const ctx existsvars
           body
           (Some 1)
           [] [] None None)
  in
  if (List.length forallvars) == 0
  then p
  else
    Quantifier.expr_of_quantifier
      (Quantifier.mk_forall_const ctx forallvars
         p
         (Some 1)
         [] [] None None)
