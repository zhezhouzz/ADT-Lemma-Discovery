Require Import ListAux.
Require Import TreeAux.
Lemma stream2consistent_Lazy0 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_member  il_1 u_1)) -> (list_member  il_0 u_1)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Lazy1 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_order  il_0 u_0 u_1)/\(list_member  il_1 u_1)) -> (list_order  il_1 u_0 u_1)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Lazy2 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_order  il_0 u_0 u_1))/\(list_member  il_1 u_1)) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Lazy3 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(list_member  il_0 u_0)/\(not (list_order  il_0 u_0 u_1))/\(list_member  il_1 u_1)) -> (list_order  il_0 u_1 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Lazy4 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_0 u_0))/\(not (list_order  il_0 u_0 u_1))/\(list_member  il_1 u_1)) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Lazy5 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Lazy6 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_member  il_0 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Lazy7 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Lazy8 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_1))) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Lazy9 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(list_member  il_0 u_0)/\(not (list_member  il_1 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Lazy10 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_0 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

