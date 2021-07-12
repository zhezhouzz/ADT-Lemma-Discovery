Require Import TreeAux.
Lemma unbset2consistent_t0 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((u_0 = i_0)/\(tree_member  it_0 u_0)/\(tree_member  it_2 u_0)) -> (tree_head  it_2 i_0)).
Proof. solve_t. Qed.

Lemma unbset2consistent_t1 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_0 = i_0))/\(tree_member  it_0 u_0)/\(tree_member  it_2 u_0)) -> (not (tree_head  it_2 u_0))).
Proof. solve_t. Qed.

Lemma unbset2consistent_t2 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((u_0 = i_0)/\(tree_member  it_1 u_0)/\(not (tree_member  it_0 u_0))/\(tree_member  it_2 u_0)) -> (tree_head  it_2 i_0)).
Proof. solve_t. Qed.

Lemma unbset2consistent_t3 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_0 = i_0))/\(tree_member  it_1 u_0)/\(not (tree_member  it_0 u_0))/\(tree_member  it_2 u_0)) -> (not (tree_head  it_2 u_0))).
Proof. solve_t. Qed.

Lemma unbset2consistent_t4 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_1 u_0))/\(not (tree_member  it_0 u_0))/\(tree_member  it_2 u_0)) -> (tree_head  it_2 u_0)).
Proof. solve_t. Qed.

Lemma unbset2consistent_t5 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_1 u_0))/\(not (tree_member  it_0 u_0))/\(tree_member  it_2 u_0)) -> (u_0 = i_0)).
Proof. solve_t. Qed.

Lemma unbset2consistent_t6 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_0))) -> (not (tree_head  it_0 u_0))).
Proof. solve_t. Qed.

Lemma unbset2consistent_t7 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_0))) -> (not (tree_member  it_0 u_0))).
Proof. solve_t. Qed.

Lemma unbset2consistent_t8 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_0))) -> (not (u_0 = i_0))).
Proof. solve_t. Qed.

Lemma unbset2consistent_t9 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_0))) -> (not (tree_member  it_1 u_0))).
Proof. solve_t. Qed.

Lemma unbset2consistent_t10 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_0))) -> (not (tree_head  it_2 u_0))).
Proof. solve_t. Qed.

