Require Import ListAux.
Require Import TreeAux.
Lemma bankersq1consistent_BankersqConcat0 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_0 u_0))/\(list_member  il_2 u_0)) -> (list_member  il_1 u_0)).
Proof. solve_concat. Qed.

Lemma bankersq1consistent_BankersqConcat1 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_2 u_0))) -> (not (list_member  il_0 u_0))).
Proof. solve_concat. Qed.

Lemma bankersq1consistent_BankersqConcat2 (il_0:list nat) (il_1:list nat) (il_2:list nat) (u_0:nat) : (concat_spec  il_0 il_1 il_2) -> (((not (list_member  il_2 u_0))) -> (not (list_member  il_1 u_0))).
Proof. solve_concat. Qed.

