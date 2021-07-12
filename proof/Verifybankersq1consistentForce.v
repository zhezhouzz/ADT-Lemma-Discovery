Require Import ListAux.
Require Import TreeAux.
Lemma bankersq1consistent_Force0 (il_0:list nat) (il_1:list nat) (u_0:nat) : (id_spec  il_0 il_1) -> (((list_member  il_0 u_0)) -> (list_member  il_1 u_0)).
Proof. solve_id. Qed.

Lemma bankersq1consistent_Force1 (il_0:list nat) (il_1:list nat) (u_0:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_0 u_0))) -> (not (list_member  il_1 u_0))).
Proof. solve_id. Qed.

