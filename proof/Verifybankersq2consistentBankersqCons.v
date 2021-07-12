Require Import ListAux.
Require Import Tactics.
Lemma bankersq2consistent_BankersqCons0 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(list_member  il_0 u_0)/\(not (list_order  il_0 u_1 u_0))/\(u_1 = i_0)/\(list_order  il_0 u_0 u_1)/\(list_order  il_1 u_0 u_1)/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (list_order  il_1 i_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons1 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(list_member  il_0 u_0)/\(not (list_order  il_0 u_1 u_0))/\(not (u_1 = i_0))/\(list_order  il_0 u_0 u_1)/\(list_order  il_1 u_0 u_1)/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons2 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(list_member  il_0 u_0)/\(not (list_order  il_0 u_0 u_1))/\(list_order  il_1 u_0 u_1)/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (u_0 = i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons3 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_order  il_1 u_0 u_1))/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (not (u_0 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons4 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons5 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(list_member  il_0 u_0)/\(not (list_order  il_1 u_0 u_1))/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (list_order  il_1 u_1 u_0)).
Proof.
  intro pushspec;
    inversion pushspec as [a b c Hhd Hmem Hord Honce]; subst;
      try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hord; try setoid_rewrite Honce;
        clear Hhd Hmem Hord Honce;
        repeat ((repeat setoid_rewrite rewrite_not_conj);
                (repeat setoid_rewrite rewrite_not_disj);
                (repeat setoid_rewrite rewrite_not_not));
        intros. destruct_pairs. left; eauto.
Qed.

Lemma bankersq2consistent_BankersqCons6 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_0 u_0))/\(not (list_order  il_1 u_0 u_1))/\(list_member  il_0 u_1)/\(list_member  il_1 u_1)) -> (not (list_member  il_1 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons7 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(list_member  il_1 u_1)) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons8 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(list_member  il_1 u_1)) -> (u_1 = i_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons9 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_1))/\(list_member  il_1 u_1)) -> (not (list_order  il_0 i_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons10 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))/\(not (list_member  il_0 u_1))/\(list_member  il_1 u_1)) -> (not (list_order  il_1 i_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons11 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons12 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_member  il_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons13 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (u_1 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons14 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons15 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (u_0 = i_0))/\(list_member  il_1 u_0)/\(not (list_member  il_1 u_1))) -> (list_member  il_0 u_0)).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons16 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (u_0 = i_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqCons17 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_member  il_0 u_0))).
Proof. solve_push; try (assert (u_0 = u_1); subst; eauto). Qed.

