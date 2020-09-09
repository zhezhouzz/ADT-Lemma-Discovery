open Printf;;
open Utils;;
open Z3;;
open Z3aux;;
open Epr;;
open Epr;;

let globalvars = [Array, "a"; Int, "x"; Int, "y"]
let dupvars = [Array, "b"; Int, "i"]
let dupvars0 = List.map (fun (tp, x) -> (tp, x ^ "0")) dupvars
let dupvars1 = List.map (fun (tp, x) -> (tp, x ^ "1")) dupvars
let pre = (globalvars @ dupvars), And [
    Pred (">=", [Length "a"; Const 0]);
    Pred ("=", [Variable "i"; Const 0]);
    Pred ("=", [Length "b"; Const 1]);
    ArrayExists ("b", Const 0, Variable "u");
    Pred ("=", [Variable "x"; Variable "u"]);
    (* Pred ("=", [Length "a"; Const 5]); *)
  ]

(* let spec = [Array, "b0"; Int, "x"; Int, "y"; Array, "b1"], And [
 *     ArrayForAll ("b0", Variable "b0_idx", Variable "u");
 *     ArrayExists ("b1", Variable "b1_idx", Variable "v");
 *     (\* Pred ("=", [Variable "b0_idx"; Variable "b1_idx"]); *\)
 *     Pred ("=", [Variable "u"; Variable "v"]);
 *     Ite (Pred ("=", [Variable "x"; Variable "y"]),
 *          Pred ("=", [Length "b1"; Length "b0"]),
 *          And [Pred ("=+", [Length "b1"; Length "b0"; Const 1]);
 *               ArrayExists ("b1", Length "b0", Variable "w");
 *               Pred ("=", [Variable "w"; Variable "y"])
 *              ]
 *         )
 *   ] *)
let spec = [Array, "b0"; Int, "x"; Int, "y"; Array, "b1"],
           And [
             ArrayExists ("b1", Const 0, Variable "o");
             Pred ("=", [Variable "o"; Variable "x"]);
             Or [
               And [Pred ("=", [Variable "x"; Variable "y"]);
                    Pred ("=", [Length "b1"; Length "b0"]);
                    ArrayForAll ("b0", Variable "b0_idx", Variable "u");
                    ArrayExists ("b1", Variable "b1_idx", Variable "v");
                    Pred ("=", [Variable "u"; Variable "v"]);
                   ];
               And [Not (Pred ("=", [Variable "x"; Variable "y"]));
                    Pred ("=+", [Length "b1"; Length "b0"; Const 1]);
                    ArrayExists ("b1", Length "b0", Variable "w");
                    Pred ("=", [Variable "w"; Variable "y"]);
                    ArrayForAll ("b0", Variable "b0_idx", Variable "u");
                    ArrayExists ("b1", Variable "b1_idx", Variable "v");
                    Pred ("=", [Variable "u"; Variable "v"]);
                   ];
           ]
  ]
let body = fun ctx spec ->
  Boolean.mk_and ctx [
    Boolean.mk_eq ctx (Arithmetic.Integer.mk_const_s ctx "y")
      (Z3Array.mk_select ctx (arrii_to_z3 ctx "a") (Arithmetic.Integer.mk_const_s ctx "i0"));
    Boolean.mk_eq ctx (Arithmetic.Integer.mk_const_s ctx "i1")
      (Arithmetic.mk_add ctx [Arithmetic.Integer.mk_const_s ctx "i0"; int_to_z3 ctx 1]);
    EprDnf.dnf_to_z3 ctx (EprDnf.todnf
                            (spec_apply spec [Array, "b0"; Int, "x"; Int, "y"; Array, "b1"]))
  ]
(* let iv = (globalvars @ dupvars), And [
 *     Implies (And [ArrayForAll ("b", Variable "b_idx", Variable "u");
 *                   Pred ("<>", [Variable "u"; Variable "x"]);],
 *              Pred ("=+", [Length "b"; Variable "i"; Const 1])
 *             );
 *     Implies (And [ArrayExists ("b", Variable "b_idx2", Variable "v");
 *                   Pred ("=", [Variable "v"; Variable "x"]);],
 *              Ite (Pred ("<", [Variable "b_idx2"; Variable "i"]),
 *                   Pred ("<=", [Length "b"; Variable "i"]),
 *                   Pred ("<=+", [Length "b"; Variable "i"; Const 1])
 *                  )
 *             )] *)

let iv = (globalvars @ dupvars),
         And [
           ArrayExists ("b", Const 0, Variable "v");
           Pred ("=", [Variable "v"; Variable "x"]);
           Pred ("<=", [Const 1; Variable "i"]);
           Pred ("<=", [Variable "i"; Length "a"]);
           Pred ("<=", [Const 1; Length "b"]);
           (* Pred ("=", [Length "a"; Const 5]); *)
           ArrayForAll ("a", Variable "a_idx", Variable "u");
           Or [
             And [ArrayExists ("b", Variable "b_idx0", Variable "vv");
                  Pred ("=", [Variable "u"; Variable "vv"]);
                  Pred ("<", [Variable "a_idx"; Variable "i"]);
                  Pred ("<>", [Variable "u"; Variable "x"]);
                  (* Pred ("=+", [Variable "b_idx0"; Variable "a_idx"; Const 1]); *)
                  Pred ("=+", [Length "b"; Variable "i"; Const 1]);
                 ];
             And [Not (Pred ("<", [Variable "a_idx"; Variable "i"]));];
             And [ArrayExists ("b", Variable "b_idx0", Variable "vv");
                  Pred ("=", [Variable "u"; Variable "vv"]);
                  Pred ("<", [Variable "a_idx"; Variable "i"]);
                  ArrayExists ("a", Variable "a_idx1", Variable "w");
                  Pred ("=", [Variable "w"; Variable "x"]);
                  Pred ("<", [Variable "a_idx1"; Variable "i"]);
                  Pred ("<=", [Length "b"; Variable "i"]);]
           ]
         ]

let post = (globalvars @ dupvars), Or [
    And [Pred ("=+", [Length "b"; Length "a"; Const 1]);
         ArrayForAll ("a", Variable "a_idx", Variable "u");
         Pred ("<>", [Variable "u"; Variable "x"]);
         ArrayExists ("b", Const 0, Variable "v");
         Pred ("=", [Variable "v"; Variable "x"]);
         Pred ("<=", [Const 0; Length "b"]);
        ];
    And [Pred ("<=", [Length "b"; Length "a"]);
         ArrayExists ("a", Variable "a_idx2", Variable "v");
         Pred ("=", [Variable "v"; Variable "x"]);
         Pred ("<=", [Const 0; Length "b"]);
        ];
  ]

let cond = (globalvars @ dupvars), Pred ("<", [Variable "i"; Length "a"])
let prog =
  Verify.Loop
    {pre; post; cond; body; spec; iv; globalvars; dupvars0; dupvars1}
;;
