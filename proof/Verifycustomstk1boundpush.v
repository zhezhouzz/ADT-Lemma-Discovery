Require Import ListAux.
Lemma customstk1bound_push0 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = i_0))/\(list_member  il_1 u_0)) -> (list_member  il_0 u_0)).
Proof. solve_push. Qed.

Lemma customstk1bound_push1 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = i_0))/\(list_member  il_1 u_0)) -> (not (list_head  il_1 u_0))).
Proof. solve_push. Qed.

Lemma customstk1bound_push2 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))) -> (not (u_0 = i_0))).
Proof. solve_push. Qed.

Lemma customstk1bound_push3 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))) -> (not (list_member  il_0 u_0))).
Proof. solve_push. Qed.

Lemma customstk1bound_push4 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_head  il_0 u_0))/\(not (list_member  il_1 u_0))) -> (not (list_head  il_1 u_0))).
Proof. solve_push. Qed.

