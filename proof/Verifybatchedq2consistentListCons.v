Require Import ListAux.
Lemma batchedq2consistent_ListCons0 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = i_0))/\(not (list_head  il_0 u_1))/\(list_member  il_0 u_0)/\(list_order  il_1 u_0 u_1)/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons1 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = i_0))/\(not (list_head  il_0 u_1))/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_0 u_0)/\(list_order  il_1 u_0 u_1)/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons2 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = i_0))/\(not (list_head  il_0 u_1))/\(not (list_member  il_0 u_0))/\(list_order  il_1 u_0 u_1)/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (u_0 = i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons3 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = i_0))/\(not (list_head  il_0 u_1))/\(not (list_member  il_0 u_0))/\(list_order  il_1 u_0 u_1)/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (list_head  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons4 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_order  il_1 u_0 u_1))/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (not (list_head  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons5 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_order  il_1 u_0 u_1))/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons6 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_0 u_1))/\(not (list_order  il_1 u_0 u_1))/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (not (u_0 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons7 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(not (u_1 = u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (not (list_member  il_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons8 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(not (list_order  il_1 u_0 u_1))/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (not (list_head  il_1 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons9 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(list_member  il_1 u_1)) -> (list_head  il_1 u_1)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons10 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(list_member  il_1 u_1)) -> (u_1 = i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons11 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_head  il_0 u_0)/\(not (list_member  il_0 u_1))/\(list_member  il_1 u_1)) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons12 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_0 u_0))/\(list_member  il_1 u_0)/\(not (list_member  il_1 u_1))) -> (not (u_1 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons13 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_0 u_0))/\(list_member  il_1 u_0)/\(not (list_member  il_1 u_1))) -> (not (list_member  il_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons14 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_0 u_0))/\(u_0 = i_0)/\(list_member  il_1 u_0)/\(not (list_member  il_1 u_1))) -> (list_head  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons15 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_0 u_0))/\(not (u_0 = i_0))/\(list_member  il_1 u_0)/\(not (list_member  il_1 u_1))) -> (list_member  il_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons16 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_0 u_0))/\(not (u_0 = i_0))/\(list_member  il_1 u_0)/\(not (list_member  il_1 u_1))) -> (not (list_head  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons17 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons18 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_head  il_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons19 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (u_1 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons20 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_1 = u_0)/\(not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_member  il_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons21 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_1 = u_0)/\(not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_head  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons22 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (u_0 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons23 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_member  il_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons24 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_member  il_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons25 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons26 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_head  il_1 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons27 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_head  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons28 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListCons29 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

