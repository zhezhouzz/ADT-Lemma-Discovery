Require Import TreeIAux.
Lemma leftisthp2consistent_maket0 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (u_1 = i_0))/\(not (treei_ancestor  iti_0 u_1 u_0))/\(treei_member  iti_0 u_0)/\(treei_ancestor  iti_2 u_1 u_0)/\(treei_member  iti_2 u_0)/\(treei_member  iti_0 u_1)/\(treei_member  iti_2 u_1)) -> (treei_ancestor  iti_1 u_1 u_0)).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket1 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (u_1 = i_0))/\(not (treei_member  iti_0 u_0))/\(treei_ancestor  iti_2 u_1 u_0)/\(treei_member  iti_2 u_0)/\(treei_member  iti_0 u_1)/\(treei_member  iti_2 u_1)) -> (treei_ancestor  iti_1 u_1 u_0)).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket2 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (u_1 = i_0))/\(not (treei_member  iti_0 u_0))/\(treei_ancestor  iti_2 u_1 u_0)/\(treei_member  iti_2 u_0)/\(treei_member  iti_0 u_1)/\(treei_member  iti_2 u_1)) -> (treei_member  iti_1 u_1)).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket3 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_ancestor  iti_2 u_1 u_0))/\(treei_member  iti_2 u_0)/\(treei_member  iti_0 u_1)/\(treei_member  iti_2 u_1)) -> (not (u_1 = i_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket4 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_ancestor  iti_2 u_1 u_0))/\(treei_member  iti_2 u_0)/\(treei_member  iti_0 u_1)/\(treei_member  iti_2 u_1)) -> (not (treei_ancestor  iti_0 u_1 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket5 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_0))/\(treei_member  iti_0 u_1)/\(treei_member  iti_2 u_1)) -> (not (treei_ancestor  iti_0 u_1 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket6 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_0))/\(treei_member  iti_0 u_1)/\(treei_member  iti_2 u_1)) -> (not (treei_member  iti_0 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket7 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_0))/\(treei_member  iti_0 u_1)/\(treei_member  iti_2 u_1)) -> (not (treei_ancestor  iti_2 u_1 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket8 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (not (treei_ancestor  iti_0 u_1 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket9 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((treei_member  iti_1 u_0)/\(treei_member  iti_1 u_1)/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (treei_member  iti_2 u_0)).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket10 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((treei_ancestor  iti_1 u_1 u_0)/\(treei_member  iti_1 u_0)/\(treei_member  iti_1 u_1)/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (treei_ancestor  iti_2 u_1 u_0)).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket11 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((u_1 = i_0)/\(not (treei_ancestor  iti_1 u_1 u_0))/\(treei_member  iti_1 u_0)/\(treei_member  iti_1 u_1)/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (treei_ancestor  iti_2 i_0 u_0)).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket12 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (u_1 = i_0))/\(not (treei_ancestor  iti_1 u_1 u_0))/\(treei_member  iti_1 u_0)/\(treei_member  iti_1 u_1)/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (not (treei_ancestor  iti_2 u_1 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket13 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((treei_ancestor  iti_2 u_1 u_0)/\(not (treei_member  iti_1 u_0))/\(treei_member  iti_1 u_1)/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (u_1 = i_0)).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket14 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((treei_ancestor  iti_2 u_1 u_0)/\(not (treei_member  iti_1 u_0))/\(treei_member  iti_1 u_1)/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (treei_member  iti_0 u_0)).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket15 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((treei_member  iti_0 u_0)/\(not (treei_ancestor  iti_2 u_1 u_0))/\(not (treei_member  iti_1 u_0))/\(treei_member  iti_1 u_1)/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (treei_member  iti_2 u_0)).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket16 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((treei_member  iti_0 u_0)/\(not (treei_ancestor  iti_2 u_1 u_0))/\(not (treei_member  iti_1 u_0))/\(treei_member  iti_1 u_1)/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (not (u_1 = i_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket17 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((treei_member  iti_2 u_0)/\(not (treei_member  iti_0 u_0))/\(not (treei_ancestor  iti_2 u_1 u_0))/\(not (treei_member  iti_1 u_0))/\(treei_member  iti_1 u_1)/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (u_0 = i_0)).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket18 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_1 u_1))/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (u_1 = i_0)).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket19 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_1 u_1))/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (not (treei_ancestor  iti_1 i_0 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket20 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((treei_ancestor  iti_2 i_0 u_0)/\(treei_member  iti_2 u_0)/\(not (treei_member  iti_1 u_1))/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (not (i_0 = u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket21 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_ancestor  iti_2 i_0 u_0))/\(treei_member  iti_2 u_0)/\(not (treei_member  iti_1 u_1))/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (i_0 = u_0)).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket22 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_0))/\(not (treei_member  iti_1 u_1))/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (not (treei_member  iti_1 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket23 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_0))/\(not (treei_member  iti_1 u_1))/\(not (treei_member  iti_0 u_1))/\(treei_member  iti_2 u_1)) -> (not (treei_ancestor  iti_2 i_0 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket24 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_1))) -> (not (treei_ancestor  iti_0 u_1 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket25 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_1))) -> (not (u_1 = i_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket26 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_1))) -> (not (treei_ancestor  iti_2 u_1 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket27 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_0 u_0))/\(treei_member  iti_2 u_0)/\(not (treei_member  iti_2 u_1))) -> (not (treei_member  iti_0 u_1))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket28 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_0 u_0))/\(treei_member  iti_2 u_0)/\(not (treei_member  iti_2 u_1))) -> (not (treei_member  iti_1 u_1))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket29 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_0))/\(not (treei_member  iti_2 u_1))) -> (not (treei_member  iti_0 u_1))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket30 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (treei_member  iti_2 u_0))/\(not (treei_member  iti_2 u_1))) -> (not (treei_member  iti_1 u_1))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket31 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (u_1 = u_0))/\(not (treei_member  iti_2 u_0))/\(not (treei_member  iti_2 u_1))) -> (not (u_0 = i_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket32 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (u_1 = u_0))/\(not (treei_member  iti_2 u_0))/\(not (treei_member  iti_2 u_1))) -> (not (treei_member  iti_0 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma leftisthp2consistent_maket33 (i_0:nat) (iti_0:treei nat) (iti_1:treei nat) (iti_2:treei nat) (u_0:nat) (u_1:nat) : (imaket_spec  i_0 iti_0 iti_1 iti_2) -> (((not (u_1 = u_0))/\(not (treei_member  iti_2 u_0))/\(not (treei_member  iti_2 u_1))) -> (not (treei_member  iti_1 u_0))).
Proof. solve_imaket; try (assert (u_0 = u_1); subst; eauto). Qed.

