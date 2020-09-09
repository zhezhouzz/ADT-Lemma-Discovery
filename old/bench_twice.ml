open Printf;;
open Utils;;
open Z3;;
open Epr;;
open Epr;;

let globalvars = [Array, "a"; Array, "b"; Array, "c"; Int, "x"; Int, "y";
                 ]
let pre = (globalvars), And [
    Pred ("<=", [Const 0; Length "a"]);
    Pred ("=", [Const 5; Length "a"]);
  ]

let spec = [Array, "a0"; Int, "x"; Array, "a1"], Or [
    And [Pred ("<=", [Length "a1"; Length "a0"]);
         ArrayExists ("a0", Variable "a0_idx", Variable "u");
         Pred ("=", [Variable "u"; Variable "x"]);
        ];
    And [Pred ("=+", [Length "a1"; Length "a0"; Const 1]);
         ArrayForAll ("a0", Variable "a0_idx2", Variable "v");
         Pred ("<>", [Variable "v"; Variable "x"]);
         ArrayExists ("a1", Const 0, Variable "w");
         Pred ("=", [Variable "w"; Variable "x"]);
        ];
  ]

let body = fun ctx specs ->
  let spec = List.nth specs 0 in
  Boolean.mk_and ctx [
    EprDnf.dnf_to_z3 ctx (EprDnf.todnf
                            (spec_apply spec
                               [Array, "a"; Int, "x"; Array, "b"]));
    EprDnf.dnf_to_z3 ctx (EprDnf.todnf
                            (spec_apply spec
                               [Array, "b"; Int, "y"; Array, "c"]));
  ]

let post = (globalvars), Or [
    And [Pred ("=", [Variable "x"; Variable "y"]);
         Pred ("<=+", [Length "c"; Length "a"; Const 1]);
        ];
    And [Pred ("<>", [Variable "x"; Variable "y"]);
         Pred ("<=+", [Length "c"; Length "a"; Const 2]);
        ];
  ]
let specs = [spec]
let prog =
  Verify.NoLoop
    {pre; post; body; specs; globalvars}
;;
