Require Import ListAux.
Require Import TreeIAux.
Lemma leftisthp1consistent_e0 (iti_0:treei nat) (u_0:nat) : (ie_spec  iti_0) -> ((True) -> (not (treei_member  iti_0 u_0))).
Proof. solve_ie. Qed.

