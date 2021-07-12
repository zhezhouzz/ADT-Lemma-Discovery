Require Import ListAux.
Require Import TreeAux.
Lemma trie1consistent_cons0 (i_0:nat) (il_0:list nat) (il_1:list nat) (u_0:nat) : (push_spec  i_0 il_0 il_1) -> (((not (list_member  il_1 u_0))) -> (not (u_0 = i_0))).
Proof. solve_push. Qed.

