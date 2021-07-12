Require Import ListAux.
Require Import TreeAux.
Lemma batchedq1consistent_ListIsEmpty0 (il_0:list nat) (b_0:bool) (u_0:nat) : (is_empty_spec  il_0 b_0) -> ((Bool.Is_true b_0) -> (not (list_member  il_0 u_0))).
Proof. solve_is_empty. Qed.

Lemma batchedq1consistent_ListIsEmpty1 (il_0:list nat) (b_0:bool) (u_0:nat) : (is_empty_spec  il_0 b_0) -> ((Bool.Is_true b_0) -> (not (list_head  il_0 u_0))).
Proof. solve_is_empty. Qed.

Lemma batchedq1consistent_ListIsEmpty2 (il_0:list nat) (b_0:bool) (u_0:nat) : (is_empty_spec  il_0 b_0) -> (((not (list_member  il_0 u_0))/\(not (Bool.Is_true b_0))) -> (not (list_head  il_0 u_0))).
Proof. solve_is_empty. Qed.

