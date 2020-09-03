open Printf;;
open Utils;;
open Z3;;
open Epr;;
open Epr;;

let globalvars = [Array, "a"; Array, "b"; Array, "c"; Array, "d"; Int, "n";
                  Int, "len1"; Int, "v0"; Int, "n1";
                 ]
let pre = (globalvars), And [
    Pred ("<", [Variable "n"; Length "a"]);
    Pred ("<", [Const 1; Variable "n"]);
    Pred ("=-", [Variable "n1"; Variable "n"; Const 1]);
    Pred ("=-", [Variable "len1"; Length "a"; Const 1]);
    Pred ("=", [Variable "v0"; Const 0]);
    (* ArrayForAll ("a", Variable "a_idx", Variable "u");
     * Pred ("=", [Variable "a_idx"; Variable "u"]);
     * Pred ("=", [Length "a"; Const 4]); *)
  ]

let spec = [Array, "a0"; Int, "start"; Int, "end"; Array, "a1"], And [
    Pred ("=", [Length "a1"; Length "a0"]);
    And [ArrayForAll ("a0", Variable "a0_idx", Variable "u");
         ArrayExists ("a1", Variable "a1_idx", Variable "v");
         Pred ("=", [Variable "u"; Variable "v"]);
         Ite (And [Pred ("<=", [Variable "start"; Variable "a0_idx"]);
                   Pred ("<=", [Variable "a0_idx"; Variable "end"]);],
              Pred ("=+-", [Variable "end"; Variable "a1_idx"; Variable "a0_idx";Variable "start";]),
              Pred ("=", [Variable "a1_idx"; Variable "a0_idx"])
             )
        ]]
let body = fun ctx specs ->
  let spec = List.nth specs 0 in
  Boolean.mk_and ctx [
    EprDnf.dnf_to_z3 ctx (EprDnf.todnf
                            (spec_apply spec
                               [Array, "a"; Int, "v0"; Int, "len1"; Array, "b"]));
    EprDnf.dnf_to_z3 ctx (EprDnf.todnf
                            (spec_apply spec
                               [Array, "b"; Int, "v0"; Int, "n1"; Array, "c"]));
    EprDnf.dnf_to_z3 ctx (EprDnf.todnf
                            (spec_apply spec
                               [Array, "c"; Int, "n"; Int, "len1"; Array, "d"]));
  ]

let post = (globalvars), And [
    Pred ("=", [Length "d"; Length "a"]);
    And [ArrayForAll ("a", Variable "a_idx", Variable "u");
         ArrayExists ("d", Variable "d_idx", Variable "v");
         Pred ("=", [Variable "u"; Variable "v"]);
         Ite (Pred (">+", [Length "a"; Variable "a_idx"; Variable "n"]),
              Pred ("=+", [Variable "d_idx"; Variable "a_idx"; Variable "n"]),
              (* Pred ("=", [Const 0; Const 0]), *)
              Pred ("=+-", [Variable "a_idx"; Variable "d_idx"; Length "a"; Variable "n"])
              (* Pred ("=", [Const 0; Const 0]) *)
             )
        ]]
let specs = [spec]
let prog =
  Verify.NoLoop
    {pre; post; body; specs; globalvars}
;;
