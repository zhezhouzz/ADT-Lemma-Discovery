Require Import ListAux.
Require Import TreeAux.
Lemma stream2consistent_Force0 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_member  il_0 u_0)/\(u_1 = u_0)) -> (list_member  il_1 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force1 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_order  il_0 u_0 u_0)/\(list_member  il_0 u_0)/\(u_1 = u_0)) -> (list_order  il_1 u_0 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force2 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_0 u_0))/\(u_1 = u_0)) -> (not (list_order  il_1 u_0 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force3 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_0 u_0))/\(u_1 = u_0)) -> (not (list_order  il_0 u_0 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force4 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_0 u_0))/\(u_1 = u_0)) -> (not (list_member  il_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force5 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_member  il_1 u_1)/\(not (u_1 = u_0))) -> (list_member  il_0 u_1)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force6 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_order  il_0 u_1 u_0)/\(list_member  il_1 u_1)/\(not (u_1 = u_0))) -> (list_order  il_1 u_1 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force7 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)/\(not (u_1 = u_0))) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force8 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_member  il_0 u_0)/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)/\(not (u_1 = u_0))) -> (list_order  il_1 u_0 u_1)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force9 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_member  il_0 u_0)/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)/\(not (u_1 = u_0))) -> (list_order  il_0 u_0 u_1)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force10 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_0 u_0))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)/\(not (u_1 = u_0))) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force11 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))/\(not (u_1 = u_0))) -> (not (list_member  il_0 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force12 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))/\(not (u_1 = u_0))) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Force13 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_0 u_0))/\(not (list_member  il_1 u_1))/\(not (u_1 = u_0))) -> (not (list_member  il_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

