open Printf;;
open Utils;;
open Z3;;
open Z3aux;;
open Epr;;
open Verify;;

let client = And [
    BApp ("pre", [AVar "l1"; AVar "l2"]);
    BApp ("spec", [AVar "l1"; AVar "l2"]);
    Not (BApp ("post", [AVar "l1"; AVar "l2"]));
  ]

let case1_pre = "pre",  ["l1";"l2"], ["u"; "v"], True

let case1_post = "post",  ["l1";"l2"], ["u"; "v"],
                 Implies (Atom (list_order "l2" "u" "v"), Atom (Bop ("<>", [AVar "u";AVar "v"])))

let spec_origin = "spec", ["l1";"l2"], ["u"; "v"], And [
    Implies (Atom (list_order "l2" "u" "v"), Atom (list_order "l1" "u" "v"));
    Implies (And [
        Atom (list_order "l1" "u" "v");
        Not (Atom (list_order "l1" "v" "u");)
      ], Atom (list_order "l2" "u" "v"));
  ]

let case1_spec_abduction = "spec", ["l1";"l2"], ["u"; "v"], And [
    Implies (Atom (list_order "l2" "u" "v"), And [
        Atom (list_order "l1" "u" "v");
        Atom (Bop ("<>", [AVar "u"; AVar "v"]))
      ]);
    Implies (And [
        Atom (list_order "l1" "u" "v");
        Not (Atom (list_order "l1" "v" "u");)
      ], Atom (list_order "l2" "u" "v"));
  ]

let case1_origin = NoLoop {client; specs=[case1_pre;case1_post;spec_origin]}
let case1_abduction = NoLoop {client; specs=[case1_pre;case1_post;case1_spec_abduction]}

let case2_pre = "pre",  ["l1";"l2"], ["u"; "v"],
                Implies (Atom (list_order "l1" "u" "v"), Atom (Bop ("<>", [AVar "u";AVar "v"])))

let case2_post = "post",  ["l1";"l2"], ["u"; "v"],
                 Implies (Atom (list_next "l1" "u" "v"), Atom (list_next "l2" "u" "v"))

let case2_spec_abduction = "spec", ["l1";"l2"], ["u"; "v"], Implies (
    And [Implies (Atom (list_order "l2" "u" "v"), Atom (Bop ("<>", [AVar "u";AVar "v"])));
         Atom (list_next "l1" "u" "v")],
      Atom (list_next "l2" "u" "v")
  )

let case2_origin = NoLoop {client; specs=[case2_pre;case2_post;spec_origin]}
let case2_abduction = NoLoop {client; specs=[case2_pre;case2_post;case2_spec_abduction]}
