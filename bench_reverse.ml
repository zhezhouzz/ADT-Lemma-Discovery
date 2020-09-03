open Printf;;
open Utils;;
open Z3;;
open Z3aux;;
open Epr;;
open Epr;;

let globalvars = [Array, "inp"]
let dupvars = [Array, "a"; Int, "i"; Int, "j"]
let dupvars0 = List.map (fun (tp, x) -> (tp, x ^ "0")) dupvars
let dupvars1 = List.map (fun (tp, x) -> (tp, x ^ "1")) dupvars
let pre = (globalvars @ dupvars), And [
    Pred ("=", [Variable "i"; Const 0]);
    Pred ("=-", [Variable "j"; Length "inp"; Const 1]);
    Pred ("=", [Length "a"; Length "inp"]);
    Implies (ArrayForAll ("inp", Variable "inp_idx", Variable "inp_e"),
             And [ArrayExists ("a", Variable "a_idx", Variable "a_e");
                  Pred ("=", [Variable "inp_e"; Variable "a_e"]);
                  Pred ("=", [Variable "inp_idx"; Variable "a_idx"]);
                 ])
  ]

let spec = [Array, "a0"; Int, "i"; Int, "j"; Array, "a1"], And [
    Pred ("=", [Length "a1"; Length "a0"]);
    ArrayForAll ("a0", Variable "a0_idx", Variable "u");
    ArrayExists ("a1", Variable "a1_idx", Variable "v");
    Pred ("=", [Variable "u"; Variable "v"]);
    Ite (Pred ("=", [Variable "a0_idx"; Variable "i"]),
         Pred ("=", [Variable "a1_idx"; Variable "j"]),
         Ite(Pred ("=", [Variable "a0_idx"; Variable "j"]),
             Pred ("=", [Variable "a1_idx"; Variable "i"]),
             Pred ("=", [Variable "a0_idx"; Variable "a1_idx"])
            )
        )
    (* Implies
     *   (ArrayForAll ("a0", Variable "a0_idx", Variable "u"),
     *    Ite (Pred ("=", [Variable "a0_idx"; Variable "i"]),
     *         ArrayExists ("a1", Variable "j", Variable "u"),
     *         Ite (Pred ("=", [Variable "a0_idx"; Variable "j"]),
     *              ArrayExists ("a1", Variable "i", Variable "u"),
     *              ArrayExists ("a1", Variable "a0_idx'", Variable "u")
     *             )
     *        )
     *   ) *)
  ]
let body = fun ctx spec ->
  Boolean.mk_and ctx [
    Boolean.mk_eq ctx (Arithmetic.Integer.mk_const_s ctx "i1")
      (Arithmetic.mk_add ctx [Arithmetic.Integer.mk_const_s ctx "i0"; int_to_z3 ctx 1]);
    Boolean.mk_eq ctx (Arithmetic.Integer.mk_const_s ctx "j1")
      (Arithmetic.mk_sub ctx [Arithmetic.Integer.mk_const_s ctx "j0"; int_to_z3 ctx 1]);
    EprDnf.dnf_to_z3 ctx (EprDnf.todnf
                            (spec_apply spec [Array, "a0"; Int, "i0"; Int, "j0"; Array, "a1"]))
  ]
  (* (globalvars @ dupvars0 @ dupvars1), And[
   *   Pred ("=+", [Variable "i1"; Variable "i0"; Const 1]);
   *   Pred ("=-", [Variable "j1"; Variable "j0"; Const 1]);
   *   EprDnf.dnf_to_z3 ctx (EprDnf.todnf
   *                           spec_apply spec [Array, "a0"; Int, "i0"; Int, "j0"; Array, "a1"])
   * ] *)
let iv = (globalvars @ dupvars), And [
    (* Pred ("=", [Length "a"; Const 4]); *)
    Pred ("=", [Length "a"; Length "inp"]);
    Pred ("=++", [Length "inp"; Variable "i";  Variable "j"; Const 1]);
    Implies (
      ArrayForAll ("inp", Variable "inp_idx", Variable "u"),
      And [
        ArrayExists ("a", Variable "a_idx", Variable "u");
        Ite (Or [Pred ("<", [Variable "inp_idx"; Variable "i"]);
                 Pred (">", [Variable "inp_idx"; Variable "j"]);],
             Pred ("=++", [Length "inp"; Variable "inp_idx";  Variable "a_idx"; Const 1]),
             Pred ("=", [Variable "inp_idx"; Variable "a_idx"])
            )
      ]
    )]
let post = (globalvars @ dupvars), Implies (
    ArrayForAll ("inp", Variable "inp_idx", Variable "u"),
    And [
      ArrayExists ("a", Variable "a_idx", Variable "u");
      Pred ("=++", [Length "inp"; Variable "inp_idx";  Variable "a_idx"; Const 1]);
    ]
  )
let cond = (globalvars @ dupvars), Pred ("<", [Variable "i"; Variable "j"])
let prog =
  Verify.Loop
    {pre; post; cond; body; spec; iv; globalvars; dupvars0; dupvars1}
;;
