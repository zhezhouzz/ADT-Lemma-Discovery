Require Import ListAux.
Lemma uniquel2consistent_cons0 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_0 u_0)) -> (list_member  il_1 u_0)).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons1 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((list_once  il_1 u_0)/\(list_member  il_0 u_0)) -> (not (u_0 = i_0))).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons2 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((list_once  il_1 u_0)/\(list_member  il_0 u_0)) -> (list_once  il_0 u_0)).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons3 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((list_once  il_1 u_0)/\(list_member  il_0 u_0)) -> (not (list_head  il_1 u_0))).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons4 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((list_once  il_0 u_0)/\(not (list_once  il_1 u_0))/\(list_member  il_0 u_0)) -> (u_0 = i_0)).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons5 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((u_0 = i_0)/\(not (list_once  il_0 u_0))/\(not (list_once  il_1 u_0))/\(list_member  il_0 u_0)) -> (list_head  il_1 i_0)).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons6 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (u_0 = i_0))/\(not (list_once  il_0 u_0))/\(not (list_once  il_1 u_0))/\(list_member  il_0 u_0)) -> (not (list_head  il_1 u_0))).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons7 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))) -> (not (list_head  il_0 u_0))).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons8 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_0 u_0))) -> (not (list_once  il_0 u_0))).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons9 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_0)/\(not (list_member  il_0 u_0))) -> (list_head  il_1 u_0)).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons10 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_0)/\(not (list_member  il_0 u_0))) -> (u_0 = i_0)).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons11 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((list_member  il_1 u_0)/\(not (list_member  il_0 u_0))) -> (list_once  il_1 i_0)).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons12 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))/\(not (list_member  il_0 u_0))) -> (not (list_once  il_1 u_0))).
Proof. solve_push. Qed.

Lemma uniquel2consistent_cons13 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))/\(not (list_member  il_0 u_0))) -> (not (u_0 = i_0))).
Proof. solve_push. Qed.

