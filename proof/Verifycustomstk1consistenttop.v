Require Import ListAux.
Require Import TreeAux.
Lemma customstk1consistent_top0 (il_0:list nat) (i_0:nat) (u_0:nat) : (top_spec  il_0 i_0) -> (((u_0 = i_0)) -> (list_member  il_0 i_0)).
Proof. solve_top. Qed.

Lemma customstk1consistent_top1 (il_0:list nat) (i_0:nat) (u_0:nat) : (top_spec  il_0 i_0) -> (((u_0 = i_0)) -> (list_head  il_0 i_0)).
Proof. solve_top. Qed.

Lemma customstk1consistent_top2 (il_0:list nat) (i_0:nat) (u_0:nat) : (top_spec  il_0 i_0) -> (((not (u_0 = i_0))) -> (not (list_head  il_0 u_0))).
Proof. solve_top. Qed.

