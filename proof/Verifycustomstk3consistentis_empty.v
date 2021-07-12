Require Import ListAux.
Require Import TreeAux.
Lemma customstk3consistent_is_empty0 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> ((Bool.Is_true b_0) -> (not (list_member  il_0 u_1))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_is_empty1 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> ((Bool.Is_true b_0) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_is_empty2 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> ((Bool.Is_true b_0) -> (not (list_member  il_0 u_0))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_is_empty3 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (u_1 = u_0))/\(list_head  il_0 u_1)/\(list_member  il_0 u_1)/\(not (Bool.Is_true b_0))) -> (not (list_head  il_0 u_0))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_is_empty4 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (u_1 = u_0))/\(list_member  il_0 u_0)/\(list_head  il_0 u_1)/\(list_member  il_0 u_1)/\(not (Bool.Is_true b_0))) -> (list_order  il_0 u_1 u_0)).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_is_empty5 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (u_1 = u_0))/\(not (list_member  il_0 u_0))/\(list_head  il_0 u_1)/\(list_member  il_0 u_1)/\(not (Bool.Is_true b_0))) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_is_empty6 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (u_1 = u_0))/\(not (list_member  il_0 u_0))/\(list_head  il_0 u_1)/\(list_member  il_0 u_1)/\(not (Bool.Is_true b_0))) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_is_empty7 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (u_1 = u_0))/\(not (list_order  il_0 u_0 u_1))/\(list_member  il_0 u_0)/\(not (list_head  il_0 u_1))/\(list_member  il_0 u_1)/\(not (Bool.Is_true b_0))) -> (not (list_head  il_0 u_0))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_is_empty8 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (u_1 = u_0))/\(not (list_order  il_0 u_0 u_1))/\(list_member  il_0 u_0)/\(not (list_head  il_0 u_1))/\(list_member  il_0 u_1)/\(not (Bool.Is_true b_0))) -> (list_order  il_0 u_1 u_0)).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_is_empty9 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (list_member  il_0 u_1))/\(not (Bool.Is_true b_0))) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_is_empty10 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (list_member  il_0 u_1))/\(not (Bool.Is_true b_0))) -> (not (list_head  il_0 u_1))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_is_empty11 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((list_head  il_0 u_0)/\(not (list_member  il_0 u_1))/\(not (Bool.Is_true b_0))) -> (list_member  il_0 u_0)).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_is_empty12 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((list_head  il_0 u_0)/\(not (list_member  il_0 u_1))/\(not (Bool.Is_true b_0))) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

