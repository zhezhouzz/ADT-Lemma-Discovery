Require Import ListAux.
Lemma customstk3consistent_push0 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push1 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (list_member  il_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push2 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_1 u_0))/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (not (u_0 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push3 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_1 u_0))/\(not (list_head  il_1 u_1))/\(list_order  il_1 u_0 u_1)/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (not (u_1 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push4 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_1 u_0))/\(not (list_head  il_1 u_1))/\(list_order  il_1 u_0 u_1)/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (list_order  il_0 u_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push5 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_1 u_0))/\(not (list_head  il_1 u_1))/\(list_head  il_0 u_1)/\(not (u_1 = u_0))/\(list_order  il_1 u_0 u_1)/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (not (list_head  il_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push6 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_1 u_0))/\(list_head  il_0 u_0)/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (not (list_member  il_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push7 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_1 u_0))/\(u_1 = i_0)/\(not (list_head  il_0 i_0))/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (not (i_0 = u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push8 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_1 u_0))/\(u_1 = i_0)/\(not (list_head  il_0 i_0))/\(list_member  il_0 i_0)/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (list_order  il_0 i_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push9 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_1 u_0))/\(u_1 = i_0)/\(not (list_head  il_0 i_0))/\(not (list_member  il_0 i_0))/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_1 u_1 u_0)/\(list_member  il_1 u_1)) -> (not (list_order  il_0 i_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push10 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push11 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_1 = i_0)/\(list_member  il_0 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push12 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_1 = i_0)/\(list_member  il_0 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (list_head  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push13 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_1 = i_0)/\(list_member  il_0 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_head  il_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push14 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = i_0))/\(list_member  il_0 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_head  il_1 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push15 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(list_head  il_0 u_1)/\(list_order  il_1 u_0 u_1)/\(not (u_1 = i_0))/\(list_member  il_0 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_member  il_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push16 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(u_0 = i_0)/\(not (list_head  il_0 i_0))/\(list_member  il_0 i_0)/\(not (list_head  il_0 u_1))/\(list_order  il_1 u_0 u_1)/\(not (u_1 = i_0))/\(list_member  il_0 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (list_order  il_0 i_0 u_1)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push17 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(u_0 = i_0)/\(not (list_head  il_0 i_0))/\(not (list_member  il_0 i_0))/\(not (list_head  il_0 u_1))/\(list_order  il_1 u_0 u_1)/\(not (u_1 = i_0))/\(list_member  il_0 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_order  il_0 i_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push18 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_order  il_1 u_0 u_1))/\(not (u_1 = i_0))/\(list_member  il_0 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (u_0 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push19 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_head  il_0 u_1))/\(not (list_order  il_1 u_0 u_1))/\(not (u_1 = i_0))/\(list_member  il_0 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_member  il_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push20 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_head  il_0 u_1))/\(not (list_order  il_1 u_0 u_1))/\(not (u_1 = i_0))/\(list_member  il_0 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push21 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (u_1 = i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push22 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_member  il_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push23 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (list_head  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push24 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_head  il_0 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push25 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push26 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_head  il_1 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push27 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push28 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_member  il_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push29 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push30 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (u_1 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push31 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_head  il_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push32 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_head  il_1 u_0))/\(list_member  il_0 u_0)/\(not (list_member  il_1 u_1))) -> (not (u_0 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push33 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_head  il_1 u_0))/\(list_member  il_0 u_0)/\(not (list_member  il_1 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push34 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(u_0 = i_0)/\(not (list_member  il_0 u_0))/\(not (list_member  il_1 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push35 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(u_0 = i_0)/\(not (list_member  il_0 u_0))/\(not (list_member  il_1 u_1))) -> (list_head  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push36 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (u_0 = i_0))/\(not (list_member  il_0 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_push37 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (u_0 = i_0))/\(not (list_member  il_0 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_head  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

