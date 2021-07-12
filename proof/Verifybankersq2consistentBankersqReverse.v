Require Import ListAux.
Require Import TreeAux.
Lemma bankersq2consistent_BankersqReverse0 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((list_order  il_0 u_0 u_1)/\(list_member  il_1 u_1)) -> (list_order  il_1 u_1 u_0)).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqReverse1 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_order  il_0 u_0 u_1))/\(list_member  il_1 u_1)) -> (list_member  il_0 u_1)).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqReverse2 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_order  il_0 u_0 u_1))/\(list_member  il_1 u_1)) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqReverse3 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(list_order  il_0 u_1 u_0)/\(not (list_order  il_0 u_0 u_1))/\(list_member  il_1 u_1)) -> (list_member  il_1 u_0)).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqReverse4 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_order  il_0 u_1 u_0))/\(not (list_order  il_0 u_0 u_1))/\(list_member  il_1 u_1)) -> (not (list_member  il_1 u_0))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqReverse5 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_order  il_0 u_1 u_0))/\(not (list_order  il_0 u_0 u_1))/\(list_member  il_1 u_1)) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqReverse6 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_member  il_0 u_1))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqReverse7 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqReverse8 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_1))) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqReverse9 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(list_member  il_0 u_0)/\(not (list_member  il_1 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma bankersq2consistent_BankersqReverse10 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (reverse_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_0 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_reverse; try (assert (u_0 = u_1); subst; eauto). Qed.

