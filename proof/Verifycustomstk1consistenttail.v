Require Import ListAux.
Require Import TreeAux.
Lemma customstk1consistent_tail0 (il_0:list nat) (il_1:list nat) (u_0:nat) : (tail_spec  il_0 il_1) -> (((not (list_member  il_1 u_0))/\(list_member  il_0 u_0)) -> (list_head  il_0 u_0)).
Proof. solve_tail. Qed.

Lemma customstk1consistent_tail1 (il_0:list nat) (il_1:list nat) (u_0:nat) : (tail_spec  il_0 il_1) -> (((not (list_member  il_0 u_0))) -> (not (list_member  il_1 u_0))).
Proof. solve_tail. Qed.

Lemma customstk1consistent_tail2 (il_0:list nat) (il_1:list nat) (u_0:nat) : (tail_spec  il_0 il_1) -> (((not (list_member  il_0 u_0))) -> (not (list_head  il_1 u_0))).
Proof. solve_tail. Qed.

