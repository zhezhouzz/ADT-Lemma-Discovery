Require Import ListAux.
Require Import Tactics.
Require Import TreeAux.
Lemma batchedq2consistent_ListIsEmpty0 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (u_1 = u_0))/\(list_order  il_0 u_0 u_1)/\(list_member  il_0 u_1)) -> (list_member  il_0 u_0)).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListIsEmpty1 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (u_1 = u_0))/\(list_head  il_0 u_1)/\(list_order  il_0 u_0 u_1)/\(list_member  il_0 u_1)) -> (not (list_head  il_0 u_0))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListIsEmpty2 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (list_order  il_0 u_0 u_1))/\(list_member  il_0 u_1)) -> (not (Bool.Is_true b_0))).
Proof.
intro nilspec;
  inversion nilspec as [a b Hhd Hmem Hord Honce]; subst; intros; intr_not;
  try destruct_pairs; auto with core. apply H.
      apply (Hmem u_1) in Z. apply Z in H0. inversion H0.
Qed.

Lemma batchedq2consistent_ListIsEmpty3 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((list_head  il_0 u_0)/\(not (list_order  il_0 u_0 u_1))/\(list_member  il_0 u_1)) -> (u_1 = u_0)).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListIsEmpty4 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (list_member  il_0 u_1))) -> (not (list_head  il_0 u_1))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListIsEmpty5 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (list_member  il_0 u_1))) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListIsEmpty6 (il_0:list nat) (b_0:bool) (u_0:nat) (u_1:nat) : (is_empty_spec  il_0 b_0) -> (((not (list_member  il_0 u_1))) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_is_empty; try (assert (u_0 = u_1); subst; eauto). Qed.

