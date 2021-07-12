Require Import ListAux.
Require Import TreeAux.
Lemma unbset3consistent_e0 (it_0:tree nat) (u_0:nat) (u_1:nat) : (e_spec  it_0) -> ((True) -> (not (tree_member  it_0 u_1))).
Proof. solve_e; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_e1 (it_0:tree nat) (u_0:nat) (u_1:nat) : (e_spec  it_0) -> (((not (u_1 = u_0))) -> (not (tree_member  it_0 u_0))).
Proof. solve_e; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_e2 (it_0:tree nat) (u_0:nat) (u_1:nat) : (e_spec  it_0) -> (((not (u_1 = u_0))) -> (not (tree_left  it_0 u_1 u_0))).
Proof. solve_e; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_e3 (it_0:tree nat) (u_0:nat) (u_1:nat) : (e_spec  it_0) -> (((not (u_1 = u_0))) -> (not (tree_left  it_0 u_0 u_1))).
Proof. solve_e; try (assert (u_0 = u_1); subst; eauto). Qed.

