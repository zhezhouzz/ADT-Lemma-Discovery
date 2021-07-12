Require Import ListAux.
Lemma batchedq1consistent_ListCons0 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))/\(list_member  il_1 u_0)) -> (list_head  il_1 u_0)).
Proof. solve_push. Qed.

Lemma batchedq1consistent_ListCons1 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))) -> (not (u_0 = i_0))).
Proof. solve_push. Qed.

Lemma batchedq1consistent_ListCons2 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))) -> (not (list_head  il_1 u_0))).
Proof. solve_push. Qed.

Lemma batchedq1consistent_ListCons3 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))) -> (not (list_member  il_0 u_0))).
Proof. solve_push. Qed.

