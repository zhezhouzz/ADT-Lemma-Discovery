Require Import ListAux.
Lemma stream1consistent_Cons0 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = i_0))/\(list_member  il_1 u_0)) -> (list_member  il_0 u_0)).
Proof. solve_push. Qed.

Lemma stream1consistent_Cons1 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))) -> (not (u_0 = i_0))).
Proof. solve_push. Qed.

Lemma stream1consistent_Cons2 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))) -> (not (list_member  il_0 u_0))).
Proof. solve_push. Qed.

