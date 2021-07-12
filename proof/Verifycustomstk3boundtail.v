Require Import ListAux.
Require Import TreeAux.
Lemma customstk3bound_tail0 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_order  il_0 u_0 u_0)/\(list_member  il_1 u_0)/\(u_1 = u_0)) -> (list_member  il_0 u_0)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail1 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_head  il_0 u_0))/\(list_order  il_0 u_0 u_0)/\(list_member  il_1 u_0)/\(u_1 = u_0)) -> (list_order  il_1 u_0 u_0)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail2 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_order  il_0 u_0 u_0))/\(list_member  il_1 u_0)/\(u_1 = u_0)) -> (list_member  il_0 u_0)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail3 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_order  il_1 u_0 u_0)/\(list_head  il_0 u_0)/\(not (list_member  il_1 u_0))/\(u_1 = u_0)) -> (list_member  il_0 u_0)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail4 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_order  il_1 u_0 u_0)/\(list_head  il_0 u_0)/\(not (list_member  il_1 u_0))/\(u_1 = u_0)) -> (not (list_head  il_1 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail5 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_order  il_1 u_0 u_0))/\(list_head  il_0 u_0)/\(not (list_member  il_1 u_0))/\(u_1 = u_0)) -> (list_member  il_0 u_0)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail6 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_order  il_1 u_0 u_0))/\(list_head  il_0 u_0)/\(not (list_member  il_1 u_0))/\(u_1 = u_0)) -> (not (list_head  il_1 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail7 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_order  il_1 u_0 u_0))/\(list_head  il_0 u_0)/\(not (list_member  il_1 u_0))/\(u_1 = u_0)) -> (not (list_order  il_0 u_0 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail8 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_head  il_0 u_0))/\(not (list_member  il_1 u_0))/\(u_1 = u_0)) -> (not (list_head  il_1 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail9 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_order  il_1 u_0 u_0)/\(not (list_head  il_0 u_0))/\(not (list_member  il_1 u_0))/\(u_1 = u_0)) -> (not (list_member  il_0 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail10 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_order  il_1 u_0 u_0)/\(not (list_head  il_0 u_0))/\(not (list_member  il_1 u_0))/\(u_1 = u_0)) -> (not (list_order  il_0 u_0 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail11 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_order  il_1 u_0 u_0))/\(not (list_head  il_0 u_0))/\(not (list_member  il_1 u_0))/\(u_1 = u_0)) -> (not (list_order  il_0 u_0 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail12 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_order  il_1 u_0 u_0))/\(not (list_head  il_0 u_0))/\(not (list_member  il_1 u_0))/\(u_1 = u_0)) -> (not (list_member  il_0 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail13 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_0 u_1)/\(not (list_head  il_0 u_1))/\(list_order  il_0 u_1 u_0)/\(list_member  il_1 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_0 u_0)/\(list_head  il_0 u_0)/\(list_order  il_1 u_0 u_1)/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (not (list_member  il_1 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail14 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_0 u_1)/\(not (list_head  il_0 u_1))/\(list_order  il_0 u_1 u_0)/\(list_member  il_1 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_0 u_0)/\(not (list_head  il_1 u_1))/\(list_head  il_0 u_0)/\(list_order  il_1 u_0 u_1)/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (list_head  il_1 u_0)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail15 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_0 u_1)/\(not (list_head  il_0 u_1))/\(list_order  il_0 u_1 u_0)/\(list_member  il_1 u_1)/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_1 u_0)/\(list_member  il_0 u_0)/\(not (list_head  il_0 u_0))/\(list_order  il_1 u_0 u_1)/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (not (list_head  il_1 u_1))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail16 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_0 u_1)/\(not (list_head  il_0 u_1))/\(list_order  il_0 u_1 u_0)/\(list_member  il_1 u_1)/\(not (list_order  il_1 u_1 u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_0 u_0))/\(not (list_head  il_0 u_0))/\(list_order  il_1 u_0 u_1)/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (list_head  il_1 u_0)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail17 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_0 u_0)/\(not (list_head  il_0 u_1))/\(not (list_order  il_1 u_1 u_0))/\(list_member  il_0 u_1)/\(list_member  il_1 u_0)/\(list_order  il_0 u_1 u_0)/\(list_head  il_0 u_0)/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (not (list_member  il_1 u_1))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail18 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_0 u_0)/\(not (list_head  il_0 u_1))/\(not (list_order  il_1 u_1 u_0))/\(not (list_head  il_1 u_1))/\(not (list_head  il_1 u_0))/\(list_member  il_0 u_1)/\(not (list_member  il_1 u_0))/\(list_order  il_0 u_1 u_0)/\(list_head  il_0 u_0)/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (not (list_member  il_1 u_1))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail19 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_0 u_0)/\(not (list_head  il_0 u_1))/\(not (list_order  il_1 u_1 u_0))/\(not (list_head  il_1 u_1))/\(not (list_head  il_1 u_0))/\(not (list_member  il_0 u_1))/\(not (list_member  il_1 u_0))/\(list_order  il_0 u_1 u_0)/\(list_head  il_0 u_0)/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (list_member  il_1 u_1)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail20 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_0 u_0)/\(not (list_head  il_0 u_1))/\(not (list_order  il_1 u_1 u_0))/\(not (list_member  il_0 u_1))/\(not (list_member  il_1 u_1))/\(list_member  il_1 u_0)/\(not (list_order  il_0 u_1 u_0))/\(list_head  il_0 u_0)/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (list_head  il_1 u_1)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail21 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_1 u_0)/\(not (list_head  il_0 u_1))/\(list_member  il_1 u_1)/\(list_head  il_1 u_1)/\(list_order  il_0 u_1 u_0)/\(list_member  il_0 u_0)/\(list_member  il_0 u_1)/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (list_head  il_1 u_0)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail22 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_1 u_0)/\(not (list_head  il_0 u_1))/\(list_member  il_1 u_1)/\(list_head  il_1 u_1)/\(list_order  il_0 u_1 u_0)/\(list_member  il_0 u_0)/\(list_member  il_0 u_1)/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (list_order  il_1 u_1 u_0)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail23 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_1 u_0)/\(not (list_member  il_1 u_1))/\(list_head  il_0 u_1)/\(not (list_head  il_1 u_1))/\(list_order  il_0 u_1 u_0)/\(list_member  il_0 u_0)/\(list_member  il_0 u_1)/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (not (list_head  il_1 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail24 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_1 u_0)/\(list_member  il_1 u_1)/\(not (list_head  il_0 u_1))/\(not (list_head  il_1 u_1))/\(list_order  il_0 u_1 u_0)/\(list_member  il_0 u_0)/\(list_member  il_0 u_1)/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (list_head  il_1 u_0)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail25 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_1 u_0)/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_0 u_0)/\(list_member  il_0 u_1)/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (not (list_member  il_1 u_1))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail26 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_member  il_1 u_0)/\(list_head  il_0 u_1)/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_0 u_0)/\(list_member  il_0 u_1)/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (list_head  il_1 u_1)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail27 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_member  il_1 u_0))/\(not (list_head  il_1 u_0))/\(list_member  il_1 u_1)/\(not (list_member  il_0 u_0))/\(list_member  il_0 u_1)/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail28 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_member  il_1 u_0))/\(not (list_head  il_1 u_0))/\(list_member  il_1 u_1)/\(not (list_member  il_0 u_0))/\(list_member  il_0 u_1)/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail29 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_member  il_1 u_0))/\(not (list_head  il_1 u_0))/\(list_head  il_0 u_1)/\(not (list_head  il_1 u_1))/\(not (list_member  il_1 u_1))/\(not (list_member  il_0 u_0))/\(list_member  il_0 u_1)/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail30 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_head  il_0 u_1))/\(not (list_member  il_1 u_1))/\(not (list_head  il_1 u_1))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_0 u_0)/\(not (list_member  il_0 u_1))/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (not (list_member  il_1 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail31 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_head  il_0 u_1))/\(not (list_member  il_1 u_1))/\(not (list_head  il_1 u_1))/\(not (list_member  il_1 u_0))/\(not (list_head  il_1 u_0))/\(not (list_member  il_0 u_0))/\(not (list_member  il_0 u_1))/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail32 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((not (list_head  il_0 u_1))/\(not (list_member  il_1 u_1))/\(not (list_head  il_1 u_1))/\(not (list_member  il_1 u_0))/\(not (list_head  il_1 u_0))/\(not (list_member  il_0 u_0))/\(not (list_member  il_0 u_1))/\(not (list_head  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_order  il_0 u_0 u_1)/\(not (u_1 = u_0))) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail33 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_order  il_0 u_1 u_0)/\(not (list_member  il_1 u_1))/\(not (list_head  il_1 u_1))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))/\(not (list_member  il_0 u_0))/\(list_head  il_0 u_1)/\(not (list_head  il_0 u_0))/\(not (list_member  il_1 u_0))/\(list_member  il_0 u_1)/\(not (list_order  il_0 u_0 u_1))/\(not (u_1 = u_0))) -> (list_head  il_1 u_0)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail34 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_order  il_0 u_1 u_0)/\(not (list_member  il_1 u_1))/\(not (list_head  il_1 u_1))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))/\(not (list_head  il_0 u_1))/\(list_member  il_1 u_0)/\(not (list_member  il_0 u_1))/\(not (list_order  il_0 u_0 u_1))/\(not (u_1 = u_0))) -> (not (list_member  il_0 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail35 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_order  il_0 u_1 u_0)/\(not (list_member  il_1 u_1))/\(not (list_head  il_1 u_1))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))/\(not (list_head  il_0 u_1))/\(not (list_head  il_1 u_0))/\(list_member  il_0 u_0)/\(not (list_member  il_1 u_0))/\(not (list_member  il_0 u_1))/\(not (list_order  il_0 u_0 u_1))/\(not (u_1 = u_0))) -> (not (list_head  il_0 u_0))).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3bound_tail36 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (tail_spec  il_0 il_1) -> (((list_order  il_0 u_1 u_0)/\(not (list_member  il_1 u_1))/\(not (list_head  il_1 u_1))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))/\(not (list_head  il_0 u_1))/\(not (list_head  il_1 u_0))/\(not (list_member  il_0 u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_0 u_1))/\(not (list_order  il_0 u_0 u_1))/\(not (u_1 = u_0))) -> (list_head  il_0 u_0)).
Proof. solve_tail; try (assert (u_0 = u_1); subst; eauto). Qed.

