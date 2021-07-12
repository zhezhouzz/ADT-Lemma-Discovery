Require Import ListAux.
Lemma stream3bound_Cons0 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(list_once  il_0 u_1)/\(not (list_order  il_0 u_0 u_1))/\(not (list_member  il_0 u_0))/\(not (list_order  il_1 u_1 u_0))/\(not (u_0 = i_0))/\(u_1 = i_0)/\(list_member  il_0 u_1)/\(list_once  il_1 u_1)/\(list_once  il_1 u_0)/\(list_order  il_1 u_0 u_1)) -> (not (list_once  il_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons1 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(list_once  il_0 u_1)/\(not (list_order  il_0 u_0 u_1))/\(not (list_member  il_0 u_0))/\(not (list_order  il_1 u_1 u_0))/\(u_0 = i_0)/\(not (list_once  il_0 i_0))/\(not (u_1 = i_0))/\(list_member  il_0 u_1)/\(list_once  il_1 u_1)/\(list_once  il_1 u_0)/\(list_order  il_1 u_0 u_1)) -> (not (list_order  il_0 u_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons2 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(not (u_0 = i_0))/\(not (list_once  il_0 i_0))/\(u_1 = i_0)/\(list_member  il_0 u_0)/\(list_once  il_0 u_0)/\(not (list_member  il_0 u_1))/\(list_once  il_1 u_1)/\(list_once  il_1 u_0)/\(list_order  il_1 u_0 u_1)) -> (not (list_order  il_0 u_0 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons3 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(u_0 = i_0)/\(not (u_1 = i_0))/\(list_member  il_0 u_0)/\(list_once  il_0 u_0)/\(not (list_member  il_0 u_1))/\(list_once  il_1 u_1)/\(list_once  il_1 u_0)/\(list_order  il_1 u_0 u_1)) -> (not (list_once  il_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons4 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(u_1 = i_0)/\(not (u_0 = i_0))/\(not (list_once  il_0 i_0))/\(list_order  il_0 i_0 u_0)/\(not (list_member  il_0 u_0))/\(list_once  il_0 u_0)/\(not (list_member  il_0 u_1))/\(list_once  il_1 u_1)/\(list_once  il_1 u_0)/\(list_order  il_1 u_0 u_1)) -> (list_order  il_0 u_0 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons5 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(u_1 = i_0)/\(not (u_0 = i_0))/\(not (list_once  il_0 i_0))/\(list_order  il_0 i_0 u_0)/\(not (list_member  il_0 u_0))/\(list_once  il_0 u_0)/\(not (list_member  il_0 u_1))/\(list_once  il_1 u_1)/\(list_once  il_1 u_0)/\(list_order  il_1 u_0 u_1)) -> (list_order  il_1 i_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons6 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(u_1 = i_0)/\(not (u_0 = i_0))/\(not (list_once  il_0 i_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 u_0))/\(list_once  il_0 u_0)/\(not (list_member  il_0 u_1))/\(list_once  il_1 u_1)/\(list_once  il_1 u_0)/\(list_order  il_1 u_0 u_1)) -> (not (list_order  il_0 u_0 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons7 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(u_0 = i_0)/\(list_once  il_0 u_1)/\(not (list_member  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_member  il_0 u_1))/\(list_once  il_1 u_1)/\(list_once  il_1 u_0)/\(list_order  il_1 u_0 u_1)) -> (list_order  il_1 u_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons8 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(u_0 = i_0)/\(list_once  il_0 u_1)/\(not (list_member  il_0 i_0))/\(list_order  il_0 u_1 i_0)/\(not (list_once  il_0 u_0))/\(not (list_member  il_0 u_1))/\(list_once  il_1 u_1)/\(list_once  il_1 u_0)/\(list_order  il_1 u_0 u_1)) -> (not (list_order  il_0 i_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons9 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(u_0 = i_0)/\(list_once  il_0 u_1)/\(not (list_member  il_0 i_0))/\(not (list_order  il_0 u_1 i_0))/\(not (list_once  il_0 u_0))/\(not (list_member  il_0 u_1))/\(list_once  il_1 u_1)/\(list_once  il_1 u_0)/\(list_order  il_1 u_0 u_1)) -> (list_order  il_0 i_0 u_1)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons10 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(u_1 = i_0)/\(not (u_0 = i_0))/\(list_once  il_0 u_0)/\(list_member  il_0 i_0)/\(not (list_member  il_0 u_0))/\(not (list_order  il_1 i_0 u_0))/\(not (list_once  il_1 u_1))/\(list_once  il_1 u_0)/\(list_order  il_1 u_0 u_1)) -> (list_once  il_0 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons11 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(u_1 = i_0)/\(not (u_0 = i_0))/\(list_once  il_0 u_0)/\(list_member  il_0 i_0)/\(not (list_member  il_0 u_0))/\(not (list_order  il_1 i_0 u_0))/\(not (list_once  il_1 u_1))/\(list_once  il_1 u_0)/\(list_order  il_1 u_0 u_1)) -> (list_order  il_0 u_0 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons12 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_0 = i_0))/\(u_1 = u_0)/\(list_once  il_0 u_0)/\(list_member  il_0 u_0)/\(not (list_once  il_1 u_0))/\(list_order  il_1 u_0 u_1)) -> (not (list_order  il_1 u_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons13 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = i_0))/\(u_0 = i_0)/\(list_once  il_0 u_1)/\(not (list_member  il_0 u_1))/\(not (u_1 = u_0))/\(list_once  il_0 u_0)/\(list_member  il_0 u_0)/\(not (list_once  il_1 u_0))/\(list_order  il_1 u_0 u_1)) -> (not (list_once  il_1 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons14 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(u_0 = i_0)/\(list_once  il_0 u_1)/\(not (list_member  il_0 u_1))/\(not (list_once  il_0 u_0))/\(list_member  il_0 u_0)/\(not (list_once  il_1 u_0))/\(list_order  il_1 u_0 u_1)) -> (not (list_once  il_1 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons15 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (list_member  il_0 u_0))/\(not (list_once  il_1 u_0))/\(list_order  il_1 u_0 u_1)) -> (not (u_1 = u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons16 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))/\(not (u_0 = i_0))/\(not (list_once  il_1 u_0))/\(list_order  il_0 u_0 u_0)/\(list_once  il_0 u_0)/\(u_1 = u_0)/\(list_order  il_1 u_1 u_0)/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons17 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))/\(not (u_0 = i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 u_0))/\(list_once  il_0 u_0)/\(u_1 = u_0)/\(list_order  il_1 u_1 u_0)/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons18 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))/\(not (u_0 = i_0))/\(list_once  il_1 u_0)/\(not (list_once  il_0 u_0))/\(u_1 = u_0)/\(list_order  il_1 u_1 u_0)/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons19 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(list_once  il_1 u_1)/\(list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(not (u_0 = i_0))/\(not (list_once  il_0 i_0))/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(list_member  il_0 u_0)/\(u_1 = i_0)/\(not (u_1 = u_0))/\(list_order  il_1 u_1 u_0)/\(not (list_order  il_1 u_0 u_1))) -> (not (list_once  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons20 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(list_once  il_1 u_1)/\(list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(u_0 = i_0)/\(list_once  il_0 u_1)/\(list_order  il_0 u_1 i_0)/\(list_once  il_0 i_0)/\(not (u_1 = i_0))/\(not (u_1 = u_0))/\(list_order  il_1 u_1 u_0)/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_0 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons21 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(list_once  il_1 u_1)/\(list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(u_0 = i_0)/\(list_once  il_0 u_1)/\(not (list_order  il_0 u_1 i_0))/\(not (list_order  il_0 i_0 u_1))/\(not (list_member  il_0 i_0))/\(not (list_once  il_0 i_0))/\(not (u_1 = i_0))/\(not (u_1 = u_0))/\(list_order  il_1 u_1 u_0)/\(not (list_order  il_1 u_0 u_1))) -> (not (list_once  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons22 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(list_once  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons23 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(i_0 = i_0)/\(not (list_once  il_0 i_0))/\(list_once  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons24 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(i_0 = i_0)/\(not (list_once  il_0 i_0))/\(list_once  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons25 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (i_0 = i_0))/\(not (list_once  il_0 i_0))/\(list_once  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons26 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(list_member  il_1 u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons27 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(i_0 = i_0)/\(not (list_once  il_0 i_0))/\(list_member  il_1 u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons28 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(i_0 = i_0)/\(not (list_once  il_0 i_0))/\(list_member  il_1 u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons29 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (i_0 = i_0))/\(not (list_once  il_0 i_0))/\(list_member  il_1 u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons30 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(u_0 = i_0)/\(not (list_member  il_1 u_0))/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons31 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_once  il_1 i_0)/\(i_0 = i_0)/\(not (list_once  il_0 i_0))/\(u_0 = i_0)/\(not (list_member  il_1 u_0))/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons32 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_1 i_0))/\(i_0 = i_0)/\(not (list_once  il_0 i_0))/\(u_0 = i_0)/\(not (list_member  il_1 u_0))/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons33 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_1 i_0))/\(not (i_0 = i_0))/\(not (list_once  il_0 i_0))/\(u_0 = i_0)/\(not (list_member  il_1 u_0))/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons34 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((i_0 = u_0)/\(not (u_0 = i_0))/\(not (list_member  il_1 u_0))/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons35 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(list_once  il_1 u_0)/\(list_member  il_0 u_0)/\(i_0 = u_0)/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons36 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 u_0)/\(i_0 = u_0)/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons37 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(list_once  il_1 u_0)/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons38 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_once  il_1 u_0))/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons39 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = u_0))/\(not (list_once  il_1 u_0))/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons40 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(list_once  il_0 i_0)/\(not (i_0 = u_0))/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons41 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(not (i_0 = u_0))/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons42 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_once  il_0 i_0))/\(not (i_0 = u_0))/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons43 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 u_0)/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons44 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(list_once  il_1 u_0)/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons45 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = u_0))/\(list_once  il_1 u_0)/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons46 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_once  il_1 u_0))/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons47 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_member  il_0 i_0)/\(not (i_0 = u_0))/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons48 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(not (list_member  il_0 i_0))/\(not (i_0 = u_0))/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons49 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_member  il_0 i_0))/\(not (i_0 = u_0))/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons50 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_once  il_1 i_0)/\(i_0 = i_0)/\(u_0 = i_0)/\(list_member  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons51 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_1 i_0))/\(i_0 = i_0)/\(u_0 = i_0)/\(list_member  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons52 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_1 i_0))/\(not (i_0 = i_0))/\(u_0 = i_0)/\(list_member  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons53 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((i_0 = u_0)/\(not (u_0 = i_0))/\(list_member  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons54 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(i_0 = i_0)/\(not (list_member  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons55 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(i_0 = i_0)/\(not (list_member  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons56 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (i_0 = i_0))/\(not (list_member  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons57 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = u_0))/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(not (list_member  il_0 i_0))/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons58 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (i_0 = u_0))/\(not (list_member  il_0 i_0))/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons59 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(i_0 = i_0)/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons60 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(i_0 = i_0)/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons61 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (i_0 = i_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons62 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(list_order  il_0 i_0 u_0)/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons63 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(list_once  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons64 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(i_0 = i_0)/\(not (list_once  il_0 i_0))/\(list_once  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons65 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(i_0 = i_0)/\(not (list_once  il_0 i_0))/\(list_once  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons66 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (i_0 = i_0))/\(not (list_once  il_0 i_0))/\(list_once  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons67 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(list_member  il_1 u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons68 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(i_0 = i_0)/\(not (list_once  il_0 i_0))/\(list_member  il_1 u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons69 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(i_0 = i_0)/\(not (list_once  il_0 i_0))/\(list_member  il_1 u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons70 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (i_0 = i_0))/\(not (list_once  il_0 i_0))/\(list_member  il_1 u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons71 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(u_0 = i_0)/\(not (list_member  il_1 u_0))/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons72 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_once  il_1 i_0)/\(i_0 = i_0)/\(not (list_once  il_0 i_0))/\(u_0 = i_0)/\(not (list_member  il_1 u_0))/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons73 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_1 i_0))/\(i_0 = i_0)/\(not (list_once  il_0 i_0))/\(u_0 = i_0)/\(not (list_member  il_1 u_0))/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons74 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_1 i_0))/\(not (i_0 = i_0))/\(not (list_once  il_0 i_0))/\(u_0 = i_0)/\(not (list_member  il_1 u_0))/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons75 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((i_0 = u_0)/\(not (u_0 = i_0))/\(not (list_member  il_1 u_0))/\(not (list_once  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons76 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(list_once  il_1 u_0)/\(list_member  il_0 u_0)/\(i_0 = u_0)/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons77 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 u_0)/\(i_0 = u_0)/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons78 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(list_once  il_1 u_0)/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons79 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_once  il_1 u_0))/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons80 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = u_0))/\(not (list_once  il_1 u_0))/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons81 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(list_once  il_0 i_0)/\(not (i_0 = u_0))/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons82 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(not (i_0 = u_0))/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons83 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_once  il_0 i_0))/\(not (i_0 = u_0))/\(not (list_member  il_0 i_0))/\(list_once  il_0 u_0)/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons84 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 u_0)/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons85 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(list_once  il_1 u_0)/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons86 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = u_0))/\(list_once  il_1 u_0)/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons87 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_once  il_1 u_0))/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons88 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_member  il_0 i_0)/\(not (i_0 = u_0))/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons89 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(not (list_member  il_0 i_0))/\(not (i_0 = u_0))/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons90 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_member  il_0 i_0))/\(not (i_0 = u_0))/\(list_once  il_0 i_0)/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons91 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_once  il_1 i_0)/\(i_0 = i_0)/\(u_0 = i_0)/\(list_member  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons92 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_1 i_0))/\(i_0 = i_0)/\(u_0 = i_0)/\(list_member  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons93 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_1 i_0))/\(not (i_0 = i_0))/\(u_0 = i_0)/\(list_member  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons94 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((i_0 = u_0)/\(not (u_0 = i_0))/\(list_member  il_1 u_0)/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons95 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(i_0 = i_0)/\(not (list_member  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons96 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(i_0 = i_0)/\(not (list_member  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons97 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (i_0 = i_0))/\(not (list_member  il_1 u_0))/\(list_member  il_0 i_0)/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons98 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = u_0))/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(not (list_member  il_0 i_0))/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons99 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (i_0 = u_0))/\(not (list_member  il_0 i_0))/\(list_once  il_1 u_0)/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons100 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(i_0 = i_0)/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons101 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(i_0 = i_0)/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons102 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (i_0 = i_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons103 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_once  il_0 i_0))/\(not (list_once  il_0 u_0))/\(not (list_order  il_0 i_0 u_0))/\(list_order  il_0 u_0 i_0)/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons104 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_member  il_0 u_0))/\(list_once  il_0 u_0)/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(list_order  il_0 i_0 u_0)/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons105 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))/\(u_0 = u_0)/\(not (list_once  il_0 u_0))/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(list_order  il_0 i_0 u_0)/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons106 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))/\(not (u_0 = u_0))/\(not (list_once  il_0 u_0))/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(list_order  il_0 i_0 u_0)/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons107 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_member  il_0 i_0)/\(not (i_0 = u_0))/\(list_once  il_0 i_0)/\(list_order  il_0 i_0 u_0)/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons108 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(not (list_member  il_0 i_0))/\(not (i_0 = u_0))/\(list_once  il_0 i_0)/\(list_order  il_0 i_0 u_0)/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons109 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_member  il_0 i_0))/\(not (i_0 = u_0))/\(list_once  il_0 i_0)/\(list_order  il_0 i_0 u_0)/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons110 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_0)/\(u_0 = u_0)/\(list_member  il_0 u_0)/\(i_0 = u_0)/\(not (list_once  il_0 i_0))/\(list_order  il_0 i_0 u_0)/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_once  il_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons111 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = u_0))/\(not (list_once  il_0 u_0))/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(not (list_once  il_0 i_0))/\(list_order  il_0 i_0 u_0)/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons112 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(list_member  il_0 i_0)/\(not (i_0 = u_0))/\(not (list_once  il_0 i_0))/\(list_order  il_0 i_0 u_0)/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons113 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_member  il_0 i_0)/\(not (i_0 = u_0))/\(not (list_once  il_0 i_0))/\(list_order  il_0 i_0 u_0)/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons114 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_member  il_0 i_0))/\(not (i_0 = u_0))/\(not (list_once  il_0 i_0))/\(list_order  il_0 i_0 u_0)/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons115 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_member  il_0 u_0))/\(list_once  il_0 u_0)/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(not (list_order  il_0 i_0 u_0))/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons116 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))/\(u_0 = u_0)/\(not (list_once  il_0 u_0))/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(not (list_order  il_0 i_0 u_0))/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons117 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))/\(not (u_0 = u_0))/\(not (list_once  il_0 u_0))/\(i_0 = u_0)/\(list_once  il_0 i_0)/\(not (list_order  il_0 i_0 u_0))/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons118 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_member  il_0 i_0)/\(not (i_0 = u_0))/\(list_once  il_0 i_0)/\(not (list_order  il_0 i_0 u_0))/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons119 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(not (list_member  il_0 i_0))/\(not (i_0 = u_0))/\(list_once  il_0 i_0)/\(not (list_order  il_0 i_0 u_0))/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons120 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_member  il_0 i_0))/\(not (i_0 = u_0))/\(list_once  il_0 i_0)/\(not (list_order  il_0 i_0 u_0))/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons121 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_once  il_0 u_0))/\(list_member  il_0 u_0)/\(i_0 = u_0)/\(not (list_once  il_0 i_0))/\(not (list_order  il_0 i_0 u_0))/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons122 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = u_0))/\(not (list_once  il_0 u_0))/\(not (list_member  il_0 u_0))/\(i_0 = u_0)/\(not (list_once  il_0 i_0))/\(not (list_order  il_0 i_0 u_0))/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons123 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(list_member  il_0 i_0)/\(not (i_0 = u_0))/\(not (list_once  il_0 i_0))/\(not (list_order  il_0 i_0 u_0))/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons124 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_member  il_0 i_0)/\(not (i_0 = u_0))/\(not (list_once  il_0 i_0))/\(not (list_order  il_0 i_0 u_0))/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons125 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_member  il_0 i_0))/\(not (i_0 = u_0))/\(not (list_once  il_0 i_0))/\(not (list_order  il_0 i_0 u_0))/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons126 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(list_once  il_0 u_0)/\(i_0 = u_0)/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons127 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))/\(not (u_0 = u_0))/\(list_once  il_0 u_0)/\(i_0 = u_0)/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons128 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(list_member  il_0 u_0)/\(list_order  il_0 u_0 u_0)/\(not (list_once  il_0 u_0))/\(i_0 = u_0)/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons129 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_member  il_0 u_0))/\(list_order  il_0 u_0 u_0)/\(not (list_once  il_0 u_0))/\(i_0 = u_0)/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons130 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(list_member  il_0 u_0)/\(not (list_order  il_0 u_0 u_0))/\(not (list_once  il_0 u_0))/\(i_0 = u_0)/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons131 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_member  il_0 u_0))/\(not (list_order  il_0 u_0 u_0))/\(not (list_once  il_0 u_0))/\(i_0 = u_0)/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons132 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(list_once  il_0 u_0)/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons133 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(list_order  il_0 i_0 i_0)/\(not (list_once  il_0 i_0))/\(list_once  il_0 u_0)/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons134 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_order  il_0 i_0 i_0)/\(not (list_once  il_0 i_0))/\(list_once  il_0 u_0)/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons135 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(not (list_order  il_0 i_0 i_0))/\(not (list_once  il_0 i_0))/\(list_once  il_0 u_0)/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons136 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_order  il_0 i_0 i_0))/\(not (list_once  il_0 i_0))/\(list_once  il_0 u_0)/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons137 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_0 i_0))/\(u_0 = i_0)/\(list_member  il_1 i_0)/\(list_order  il_0 i_0 u_0)/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_once  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons138 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_0 u_0)/\(not (list_member  il_1 u_0))/\(not (u_0 = i_0))/\(list_member  il_1 i_0)/\(list_order  il_0 i_0 u_0)/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_once  il_0 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons139 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_0 u_0)/\(not (list_member  il_1 u_0))/\(not (u_0 = i_0))/\(list_member  il_1 i_0)/\(list_order  il_0 i_0 u_0)/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_once  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons140 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_member  il_1 i_0))/\(list_order  il_0 i_0 u_0)/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_once  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons141 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(not (list_order  il_0 i_0 u_0))/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons142 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_0 u_0)/\(u_0 = i_0)/\(list_member  il_1 i_0)/\(not (list_once  il_0 i_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_once  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons143 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_0 u_0)/\(not (list_once  il_1 i_0))/\(not (u_0 = i_0))/\(list_member  il_1 i_0)/\(not (list_once  il_0 i_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons144 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_member  il_1 i_0))/\(not (list_once  il_0 i_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(list_member  il_0 i_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_once  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons145 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(list_member  il_0 u_0)/\(list_once  il_0 u_0)/\(i_0 = u_0)/\(list_order  il_0 i_0 u_0)/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons146 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_member  il_0 u_0))/\(list_once  il_0 u_0)/\(i_0 = u_0)/\(list_order  il_0 i_0 u_0)/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons147 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = u_0))/\(not (list_member  il_0 u_0))/\(list_once  il_0 u_0)/\(i_0 = u_0)/\(list_order  il_0 i_0 u_0)/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons148 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_once  il_0 u_0))/\(i_0 = u_0)/\(list_order  il_0 i_0 u_0)/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons149 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(list_once  il_0 i_0)/\(not (i_0 = u_0))/\(list_order  il_0 i_0 u_0)/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons150 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(not (i_0 = u_0))/\(list_order  il_0 i_0 u_0)/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons151 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_once  il_0 i_0))/\(not (i_0 = u_0))/\(list_order  il_0 i_0 u_0)/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons152 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(list_member  il_0 u_0)/\(list_once  il_0 u_0)/\(i_0 = u_0)/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons153 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_member  il_0 u_0))/\(list_once  il_0 u_0)/\(i_0 = u_0)/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons154 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = u_0))/\(not (list_member  il_0 u_0))/\(list_once  il_0 u_0)/\(i_0 = u_0)/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons155 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = u_0)/\(not (list_once  il_0 u_0))/\(i_0 = u_0)/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons156 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(list_once  il_0 i_0)/\(list_once  il_0 u_0)/\(not (i_0 = u_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons157 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(list_once  il_0 u_0)/\(not (i_0 = u_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons158 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_once  il_0 i_0))/\(list_once  il_0 u_0)/\(not (i_0 = u_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons159 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(list_once  il_0 i_0)/\(list_member  il_0 u_0)/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons160 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(list_member  il_0 u_0)/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons161 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_1 i_0))/\(u_0 = i_0)/\(not (list_once  il_0 i_0))/\(list_member  il_0 u_0)/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons162 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((list_once  il_1 i_0)/\(list_member  il_1 i_0)/\(not (u_0 = i_0))/\(not (list_once  il_0 i_0))/\(list_member  il_0 u_0)/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons163 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(list_once  il_1 i_0)/\(list_once  il_0 i_0)/\(not (list_member  il_0 u_0))/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons164 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(list_once  il_0 i_0)/\(not (list_member  il_0 u_0))/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons165 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_1 i_0))/\(not (list_once  il_0 i_0))/\(not (list_member  il_0 u_0))/\(not (list_once  il_0 u_0))/\(not (i_0 = u_0))/\(not (list_order  il_0 i_0 u_0))/\(not (list_member  il_0 i_0))/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 i_0))/\(u_1 = i_0)/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons166 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = i_0))/\(list_once  il_0 u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 u_0)/\(u_1 = u_0)/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons167 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = i_0))/\(not (list_once  il_0 u_0))/\(list_once  il_1 u_0)/\(list_order  il_0 u_0 u_0)/\(not (list_member  il_0 u_0))/\(u_1 = u_0)/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons168 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = i_0))/\(list_once  il_0 u_0)/\(not (list_once  il_1 u_0))/\(list_order  il_0 u_0 u_0)/\(not (list_member  il_0 u_0))/\(u_1 = u_0)/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons169 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = i_0))/\(not (list_once  il_0 u_0))/\(list_once  il_1 u_0)/\(not (list_order  il_0 u_0 u_0))/\(not (list_member  il_0 u_0))/\(u_1 = u_0)/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons170 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = i_0))/\(list_once  il_0 u_0)/\(not (list_once  il_1 u_0))/\(not (list_order  il_0 u_0 u_0))/\(not (list_member  il_0 u_0))/\(u_1 = u_0)/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons171 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_0 u_1))/\(not (list_once  il_1 u_1))/\(not (list_member  il_1 u_1))/\(list_member  il_1 u_0)/\(list_member  il_0 u_1)/\(list_member  il_0 i_0)/\(list_once  il_0 i_0)/\(u_0 = i_0)/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_order  il_0 u_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons172 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_0 u_1))/\(not (list_once  il_1 u_1))/\(not (list_member  il_1 u_1))/\(list_member  il_1 u_0)/\(list_member  il_0 u_1)/\(list_member  il_0 i_0)/\(list_once  il_0 i_0)/\(u_0 = i_0)/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_order  il_0 i_0 u_1)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons173 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_0 u_1))/\(not (list_once  il_1 u_1))/\(not (list_member  il_1 u_1))/\(list_member  il_1 u_0)/\(list_member  il_0 u_1)/\(list_member  il_0 i_0)/\(list_order  il_0 u_1 i_0)/\(list_order  il_0 i_0 u_1)/\(not (list_once  il_0 i_0))/\(u_0 = i_0)/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_once  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons174 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_0 u_1))/\(not (list_once  il_1 u_1))/\(not (list_member  il_1 u_1))/\(list_member  il_1 u_0)/\(list_member  il_0 u_1)/\(not (list_member  il_0 i_0))/\(list_order  il_0 u_1 i_0)/\(list_order  il_0 i_0 u_1)/\(not (list_once  il_0 i_0))/\(u_0 = i_0)/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_once  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons175 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_0 u_1))/\(not (list_once  il_1 u_1))/\(not (list_member  il_1 u_1))/\(list_member  il_1 u_0)/\(list_member  il_0 u_1)/\(not (list_member  il_0 i_0))/\(not (list_order  il_0 u_1 i_0))/\(list_order  il_0 i_0 u_1)/\(not (list_once  il_0 i_0))/\(u_0 = i_0)/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_once  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons176 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_0 u_1))/\(not (list_once  il_1 u_1))/\(not (list_member  il_1 u_1))/\(list_member  il_1 u_0)/\(list_member  il_0 u_1)/\(list_order  il_0 u_1 i_0)/\(list_member  il_0 i_0)/\(not (list_order  il_0 i_0 u_1))/\(not (list_once  il_0 i_0))/\(u_0 = i_0)/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (list_once  il_1 i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons177 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_0 u_1))/\(not (list_once  il_1 u_1))/\(not (list_member  il_1 u_1))/\(list_member  il_1 u_0)/\(list_member  il_0 u_1)/\(list_order  il_0 u_1 i_0)/\(not (list_member  il_0 i_0))/\(not (list_order  il_0 i_0 u_1))/\(not (list_once  il_0 i_0))/\(u_0 = i_0)/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_once  il_1 i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3bound_Cons178 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_once  il_0 u_1))/\(not (list_once  il_1 u_1))/\(not (list_member  il_1 u_1))/\(list_member  il_1 u_0)/\(list_once  il_0 u_0)/\(list_order  il_0 u_0 u_1)/\(not (list_member  il_0 u_1))/\(list_member  il_0 u_0)/\(not (u_0 = i_0))/\(not (u_1 = u_0))/\(not (u_1 = i_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_order  il_1 u_0 u_1))) -> (not (list_once  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

