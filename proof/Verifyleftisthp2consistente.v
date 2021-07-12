Require Import ListAux.
Require Import TreeIAux.
Lemma leftisthp2consistent_e0 (iti_0:treei nat) (u_0:nat) (u_1:nat) : (ie_spec  iti_0) -> ((True) -> (not (treei_member  iti_0 u_1))).
Proof. solve_ie; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_e1 (iti_0:treei nat) (u_0:nat) (u_1:nat) : (ie_spec  iti_0) -> ((True) -> (not (treei_member  iti_0 u_0))).
Proof. solve_ie; try (assert (u_0 = u_1); subst; eauto). Qed.

