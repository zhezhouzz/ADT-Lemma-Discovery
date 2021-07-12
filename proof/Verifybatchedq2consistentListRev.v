Require Import ListAux.
Require Import TreeAux.
Require Import Tactics.
Lemma batchedq2consistent_ListRev0 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((list_member  il_0 u_1)) -> (list_member  il_1 u_1)).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev1 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_head  il_0 u_1))/\(list_order  il_0 u_1 u_0)/\(list_member  il_0 u_1)) -> (list_order  il_1 u_0 u_1)).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev2 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_head  il_0 u_1))/\(not (list_order  il_0 u_0 u_1))/\(list_order  il_0 u_1 u_0)/\(list_member  il_0 u_1)) -> (not (list_head  il_1 u_1))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev3 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_head  il_0 u_1))/\(not (list_order  il_0 u_0 u_1))/\(list_order  il_0 u_1 u_0)/\(list_member  il_0 u_1)) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev4 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_order  il_0 u_1 u_0))/\(list_member  il_0 u_1)) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev5 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_0 u_1)) -> (not (list_head  il_1 u_0))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev6 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_head  il_1 u_1))/\(list_order  il_0 u_0 u_1)/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_0 u_1)) -> (list_member  il_0 u_0)).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev7 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_head  il_1 u_1))/\(list_order  il_0 u_0 u_1)/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_0 u_1)) -> (list_order  il_1 u_1 u_0)).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev8 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_order  il_0 u_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_0 u_1)) -> (not (list_member  il_0 u_0))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev9 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_head  il_0 u_1))/\(not (list_order  il_0 u_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_0 u_1)) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev10 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_head  il_0 u_1))/\(not (list_order  il_0 u_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_0 u_1)) -> (not (list_head  il_0 u_0))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev11 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_member  il_0 u_1))) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev12 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_member  il_0 u_1))) -> (not (list_member  il_1 u_1))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev13 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_member  il_0 u_1))) -> (not (list_head  il_0 u_1))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev14 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_member  il_0 u_1))) -> (not (list_head  il_1 u_1))).
Proof.
  intro pushspec;
  inversion pushspec as [a b Hhd Hmem Hord Honce Hhd' Hhd'']; subst;
    try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hord; try setoid_rewrite Honce.
  intros. intro. eauto.
Qed.

Lemma batchedq2consistent_ListRev15 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_member  il_0 u_1))) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev16 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(list_member  il_1 u_0)/\(not (list_member  il_0 u_1))) -> (list_member  il_0 u_0)).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev17 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_0 u_1))) -> (not (list_member  il_0 u_0))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev18 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_0 u_1))) -> (not (list_head  il_0 u_0))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma batchedq2consistent_ListRev19 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_0 u_1))) -> (not (list_head  il_1 u_0))).
Proof.
  intro pushspec;
    inversion pushspec as [a b Hhd Hmem Hord Honce Hhd' Hhd'']; subst;
      try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hord; try setoid_rewrite Honce.
  intros; destruct_pairs. intro. eauto.
Qed.

