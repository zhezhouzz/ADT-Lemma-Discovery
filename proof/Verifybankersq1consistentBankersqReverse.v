Require Import ListAux.
Require Import TreeAux.
Lemma bankersq1consistent_BankersqReverse0 (il_0:list nat) (il_1:list nat) (u_0:nat) : (reverse_spec  il_0 il_1) -> (((list_member  il_0 u_0)) -> (list_member  il_1 u_0)).
Proof. solve_reverse. Qed.

Lemma bankersq1consistent_BankersqReverse1 (il_0:list nat) (il_1:list nat) (u_0:nat) : (reverse_spec  il_0 il_1) -> (((not (list_member  il_0 u_0))) -> (not (list_member  il_1 u_0))).
Proof. solve_reverse. Qed.

