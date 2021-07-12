Require Import ListAux.
Require Import TreeAux.
Lemma unbset2consistent_e0 (it_0:tree nat) (u_0:nat) : (e_spec  it_0) -> ((True) -> (not (tree_member  it_0 u_0))).
Proof. solve_e. Qed.

Lemma unbset2consistent_e1 (it_0:tree nat) (u_0:nat) : (e_spec  it_0) -> ((True) -> (not (tree_head  it_0 u_0))).
Proof. solve_e. Qed.

