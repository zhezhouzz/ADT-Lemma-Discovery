Require Import ListAux.
Require Import Arith.
Require Import Tactics.
Lemma bankersq2consistent_BankersqConcat0 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((list_order  il_2 u_1 u_0)/\(list_member  il_0 u_1)) -> (list_member  il_2 u_0)).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat1 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((list_order  il_2 u_1 u_0)/\(list_member  il_0 u_1)) -> (list_member  il_2 u_1)).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat2 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_1 u_0))/\(u_1 = u_0)/\(list_order  il_2 u_1 u_0)/\(list_member  il_0 u_1)) -> (list_order  il_0 u_0 u_0)).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat3 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_0 u_0))/\(list_order  il_2 u_0 u_1)/\(list_member  il_1 u_1)/\(not (u_1 = u_0))/\(list_order  il_2 u_1 u_0)/\(list_member  il_0 u_1)) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat4 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_order  il_2 u_0 u_1))/\(list_member  il_1 u_1)/\(not (u_1 = u_0))/\(list_order  il_2 u_1 u_0)/\(list_member  il_0 u_1)) -> (list_order  il_1 u_1 u_0)).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat5 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_order  il_2 u_0 u_1))/\(list_member  il_1 u_1)/\(not (u_1 = u_0))/\(list_order  il_2 u_1 u_0)/\(list_member  il_0 u_1)) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat6 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_order  il_0 u_0 u_1))/\(not (list_member  il_1 u_1))/\(not (u_1 = u_0))/\(list_order  il_2 u_1 u_0)/\(list_member  il_0 u_1)) -> (not (list_order  il_2 u_0 u_1))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat7 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_order  il_0 u_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(not (list_member  il_1 u_1))/\(not (u_1 = u_0))/\(list_order  il_2 u_1 u_0)/\(list_member  il_0 u_1)) -> (not (list_member  il_0 u_0))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat8 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_order  il_2 u_1 u_0))/\(list_member  il_0 u_1)) -> (not (list_member  il_1 u_0))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat9 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_order  il_2 u_1 u_0))/\(list_member  il_0 u_1)) -> (list_member  il_2 u_1)).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat10 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_order  il_0 u_0 u_1))/\(not (list_order  il_2 u_1 u_0))/\(list_member  il_0 u_1)) -> (not (list_order  il_2 u_0 u_1))).
Proof.
    intro pushspec;
  inversion pushspec as [a b c Hhd Hmem Hord Honce]; subst;
  try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hord; try setoid_rewrite Honce;
  clear Hhd Hmem Hord Honce;
  repeat ((repeat setoid_rewrite rewrite_not_conj);
          (repeat setoid_rewrite rewrite_not_disj);
          (repeat setoid_rewrite rewrite_not_not)).
    intros. destruct H. destruct H0. destruct H0. destruct H2. destruct H3.
    - exfalso. eauto.
    - split; auto. split; eauto.
      + destruct (Nat.eqb_spec u_0 u_1).
        subst. right. eauto.
        left. intro. eauto.
Qed.

Lemma bankersq2consistent_BankersqConcat11 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_order  il_0 u_0 u_1))/\(list_member  il_2 u_0)/\(not (list_order  il_2 u_1 u_0))/\(list_member  il_0 u_1)) -> (u_1 = u_0)).
Proof.
  intro pushspec;
    inversion pushspec as [a b c Hhd Hmem Hord Honce]; subst;
      try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hord; try setoid_rewrite Honce;
        clear Hhd Hmem Hord Honce;
        repeat ((repeat setoid_rewrite rewrite_not_conj);
                (repeat setoid_rewrite rewrite_not_disj);
                (repeat setoid_rewrite rewrite_not_not));
        intros; destruct_pairs; auto with core;
          try (match goal with
               | u: nat, v: nat |- _ => destruct (Nat.eqb_spec u v); subst; auto with core
               end).
  destruct H0. exfalso. eauto. destruct H4. exfalso. eauto. exfalso. eauto.
Qed.

Lemma bankersq2consistent_BankersqConcat12 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_0 u_1))) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat13 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_0 u_1))) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat14 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((list_order  il_1 u_0 u_1)/\(list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (list_order  il_2 u_0 u_1)).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat15 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (u_1 = u_0))/\(list_order  il_1 u_1 u_0)/\(list_member  il_0 u_0)/\(list_order  il_1 u_0 u_1)/\(list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (list_order  il_2 u_1 u_0)).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat16 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (u_1 = u_0))/\(not (list_order  il_1 u_1 u_0))/\(not (list_member  il_0 u_0))/\(list_order  il_1 u_0 u_1)/\(list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (not (list_order  il_2 u_1 u_0))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat17 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((list_order  il_2 u_0 u_1)/\(not (list_order  il_1 u_0 u_1))/\(list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (list_member  il_0 u_0)).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat18 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((list_order  il_2 u_0 u_1)/\(not (list_order  il_1 u_0 u_1))/\(list_member  il_1 u_1)/\(list_member  il_1 u_0)/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (list_order  il_2 u_1 u_0)).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat19 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_1 u_1))/\(list_member  il_1 u_0)/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (not (list_order  il_2 u_1 u_0))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat20 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_0 u_0))/\(not (list_member  il_1 u_1))/\(list_member  il_1 u_0)/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat21 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_0 u_0))/\(not (list_member  il_1 u_1))/\(list_member  il_1 u_0)/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat22 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_1 u_0))/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (list_member  il_0 u_0)).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat23 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_1 u_0))/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (not (list_order  il_2 u_1 u_0))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat24 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_1 u_0))/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat25 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_1 u_0))/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (not (u_1 = u_0))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat26 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((list_member  il_1 u_1)/\(not (list_member  il_1 u_0))/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (list_member  il_2 u_1)).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat27 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_1 u_1))/\(not (list_member  il_1 u_0))/\(list_member  il_2 u_0)/\(not (list_member  il_0 u_1))) -> (not (list_member  il_2 u_1))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat28 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_2 u_0))/\(not (list_member  il_0 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat29 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_2 u_0))/\(not (list_member  il_0 u_1))) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat30 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (u_1 = u_0))/\(not (list_member  il_2 u_0))/\(not (list_member  il_0 u_1))) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat31 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (u_1 = u_0))/\(not (list_member  il_2 u_0))/\(not (list_member  il_0 u_1))) -> (not (list_member  il_0 u_0))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat32 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (u_1 = u_0))/\(not (list_member  il_2 u_0))/\(not (list_member  il_0 u_1))) -> (not (list_order  il_2 u_0 u_1))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat33 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (u_1 = u_0))/\(list_member  il_1 u_1)/\(not (list_member  il_2 u_0))/\(not (list_member  il_0 u_1))) -> (list_member  il_2 u_1)).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqConcat34 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) (u_1:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_1))/\(not (list_member  il_2 u_0))/\(not (list_member  il_0 u_1))) -> (not (list_member  il_2 u_1))).
Proof. solve_concat; try (assert (u_0 = u_1); subst; eauto). Qed.

