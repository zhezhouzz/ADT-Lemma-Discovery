Require Import ListAux.
Require Import Tactics.
Lemma stream2consistent_Cons0 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (list_member  il_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons1 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 i_0))/\(u_1 = i_0)/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (not (list_order  il_0 u_0 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons2 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 i_0))/\(u_1 = i_0)/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (not (list_order  il_1 u_0 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons3 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = i_0))/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (list_order  il_0 u_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons4 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_order  il_0 u_0 u_1))/\(not (u_1 = i_0))/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (not (u_1 = u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons5 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_order  il_0 u_0 u_1))/\(u_0 = i_0)/\(not (u_1 = i_0))/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (list_order  il_1 i_0 u_1)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons6 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_order  il_0 u_0 u_1))/\(not (u_0 = i_0))/\(not (u_1 = i_0))/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons7 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons8 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_order  il_1 u_0 u_1)/\(list_member  il_1 u_0)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (u_1 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons9 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_order  il_1 u_0 u_1)/\(list_member  il_1 u_0)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (list_member  il_0 u_1)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons10 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_order  il_1 u_0 u_1))/\(list_member  il_1 u_0)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (u_1 = u_0)).
Proof. intros. destruct_pairs. apply (lord_ord_mem1 il_1); auto. Qed.

Lemma stream2consistent_Cons11 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_order  il_1 u_0 u_1))/\(list_member  il_1 u_0)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_member  il_0 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons12 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = i_0))/\(not (list_order  il_1 u_0 u_1))/\(list_member  il_1 u_0)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (list_member  il_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons13 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(not (list_member  il_1 u_0))/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (u_1 = i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons14 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(not (list_member  il_1 u_0))/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_order  il_0 u_0 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons15 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (u_1 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons16 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons17 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_member  il_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons18 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons19 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))/\(not (u_1 = u_0))/\(u_0 = i_0)/\(not (list_member  il_1 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream2consistent_Cons20 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))/\(not (u_1 = u_0))/\(not (u_0 = i_0))/\(not (list_member  il_1 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

