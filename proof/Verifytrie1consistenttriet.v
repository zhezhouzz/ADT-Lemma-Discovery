Require Import ListAux.
Require Import TreeAux.
Lemma trie1consistent_triet0 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_0 = i_0))/\(not (tree_member  it_0 u_0))/\(tree_member  it_2 u_0)) -> (tree_member  it_1 u_0)).
Proof. solve_t. Qed.

Lemma trie1consistent_triet1 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_0))) -> (not (tree_member  it_0 u_0))).
Proof. solve_t. Qed.

Lemma trie1consistent_triet2 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_0))) -> (not (u_0 = i_0))).
Proof. solve_t. Qed.

Lemma trie1consistent_triet3 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_0))) -> (not (tree_member  it_1 u_0))).
Proof. solve_t. Qed.

