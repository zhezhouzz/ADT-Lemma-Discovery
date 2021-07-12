Require Import TreeAux.
Lemma unbset3consistent_t0 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_member  it_2 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t1 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_0 u_1 i_0))/\(tree_left  it_1 u_1 i_0)/\(u_0 = i_0)/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_member  it_1 u_1)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t2 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_0 u_1 i_0))/\(tree_left  it_1 u_1 i_0)/\(u_0 = i_0)/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_left  it_2 u_1 i_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t3 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_0 u_1 i_0))/\(not (tree_member  it_0 i_0))/\(not (tree_left  it_1 u_1 i_0))/\(u_0 = i_0)/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_left  it_2 u_1 i_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t4 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_0 u_1 i_0))/\(not (tree_member  it_0 i_0))/\(tree_member  it_1 i_0)/\(not (tree_left  it_1 u_1 i_0))/\(u_0 = i_0)/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_left  it_0 i_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t5 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_0 u_1 i_0))/\(not (tree_member  it_0 i_0))/\(tree_member  it_1 i_0)/\(not (tree_member  it_1 u_1))/\(not (tree_left  it_1 u_1 i_0))/\(u_0 = i_0)/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_left  it_1 i_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t6 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_0 u_0 u_0))/\(u_1 = u_0)/\(tree_member  it_0 u_0)/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_member  it_1 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t7 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_0 u_0 u_0))/\(u_1 = u_0)/\(tree_member  it_0 u_0)/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_left  it_1 u_0 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t8 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_1 u_0 u_1))/\(not (u_1 = u_0))/\(tree_member  it_0 u_0)/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_left  it_0 u_0 u_1)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t9 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_1 u_0 u_1))/\(not (tree_member  it_1 u_0))/\(not (u_1 = i_0))/\(tree_left  it_0 u_1 u_0)/\(not (u_1 = u_0))/\(tree_member  it_0 u_0)/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_left  it_2 u_1 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t10 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_1 u_0 u_1))/\(not (tree_member  it_1 u_0))/\(not (u_1 = i_0))/\(not (tree_left  it_0 u_1 u_0))/\(not (u_1 = u_0))/\(tree_member  it_0 u_0)/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_left  it_2 u_1 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t11 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_0 u_0))/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_member  it_1 u_1)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t12 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_0 u_0))/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_left  it_1 u_0 u_1)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t13 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((u_1 = i_0)/\(not (tree_member  it_0 u_0))/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (i_0 = u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t14 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((u_1 = i_0)/\(not (tree_member  it_0 u_0))/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_left  it_0 i_0 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t15 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((u_1 = i_0)/\(not (tree_member  it_0 u_0))/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_left  it_0 u_0 i_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t16 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((u_1 = i_0)/\(not (tree_member  it_0 u_0))/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_member  it_1 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t17 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_left  it_1 i_0 u_0)/\(u_1 = i_0)/\(not (tree_member  it_0 u_0))/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_left  it_2 i_0 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t18 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_1 i_0 u_0))/\(u_1 = i_0)/\(not (tree_member  it_0 u_0))/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_left  it_2 i_0 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t19 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_1 u_1 u_0))/\(not (u_1 = i_0))/\(not (tree_member  it_0 u_0))/\(not (u_0 = i_0))/\(tree_left  it_2 u_0 u_1)/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_left  it_2 u_1 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t20 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_2 u_0 u_1))/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (u_0 = i_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t21 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_2 u_0 u_1))/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_left  it_0 u_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t22 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_2 u_0 u_1))/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_left  it_1 u_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t23 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_1 u_1 u_0))/\(tree_left  it_2 u_1 u_0)/\(not (tree_left  it_2 u_0 u_1))/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_member  it_0 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t24 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_1 u_1 u_0))/\(not (tree_left  it_0 u_1 u_0))/\(tree_left  it_2 u_1 u_0)/\(not (tree_left  it_2 u_0 u_1))/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (u_1 = i_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t25 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_2 u_0 u_1))/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_left  it_1 u_1 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t26 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_2 u_0 u_1))/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_left  it_0 u_1 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t27 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((u_1 = i_0)/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_2 u_0 u_1))/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_member  it_0 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t28 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_member  it_1 i_0)/\(not (tree_member  it_1 u_0))/\(u_1 = i_0)/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_2 u_0 u_1))/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_member  it_2 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t29 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(not (tree_member  it_0 u_0))/\(tree_member  it_2 u_0)/\(tree_member  it_1 u_1)/\(not (u_1 = i_0))/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_2 u_0 u_1))/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (tree_member  it_1 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t30 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(not (tree_member  it_2 u_0))/\(tree_member  it_1 u_1)/\(not (u_1 = i_0))/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_2 u_0 u_1))/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_member  it_0 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t31 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(not (tree_member  it_2 u_0))/\(not (tree_member  it_1 u_1))/\(not (u_1 = i_0))/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_2 u_0 u_1))/\(tree_member  it_0 u_1)/\(tree_member  it_2 u_1)) -> (not (tree_member  it_0 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t32 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_0 u_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t33 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_0 u_1 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t34 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (tree_member  it_2 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t35 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_left  it_1 u_1 u_0)/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (tree_left  it_2 u_1 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t36 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(tree_left  it_1 u_0 u_1)/\(tree_left  it_1 u_1 u_0)/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (tree_left  it_2 u_0 u_1)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t37 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(not (tree_left  it_1 u_0 u_1))/\(tree_left  it_1 u_1 u_0)/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_2 u_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t38 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_left  it_2 u_1 u_0)/\(not (tree_left  it_1 u_1 u_0))/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (u_1 = i_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t39 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_left  it_2 u_1 u_0)/\(not (tree_left  it_1 u_1 u_0))/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (tree_member  it_0 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t40 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_left  it_2 u_1 u_0)/\(not (tree_left  it_1 u_1 u_0))/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (i_0 = u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t41 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_left  it_2 u_1 u_0)/\(not (tree_left  it_1 u_1 u_0))/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (u_0 = i_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t42 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_left  it_1 u_0 i_0)/\(tree_left  it_2 u_1 u_0)/\(not (tree_left  it_1 u_1 u_0))/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (tree_left  it_2 u_0 i_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t43 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_left  it_1 u_0 i_0))/\(tree_left  it_2 u_1 u_0)/\(not (tree_left  it_1 u_1 u_0))/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_2 u_0 i_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t44 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(u_1 = i_0)/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_1 u_1 u_0))/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_member  it_0 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t45 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(not (tree_left  it_1 u_0 i_0))/\(u_1 = i_0)/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_1 u_1 u_0))/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_2 u_0 i_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t46 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(not (tree_left  it_1 i_0 u_1))/\(tree_member  it_0 i_0)/\(u_0 = i_0)/\(not (u_1 = i_0))/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_1 u_1 u_0))/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_2 i_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t47 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(tree_left  it_1 i_0 u_1)/\(not (tree_member  it_0 i_0))/\(u_0 = i_0)/\(not (u_1 = i_0))/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_1 u_1 u_0))/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (tree_left  it_2 i_0 u_1)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t48 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(not (tree_left  it_1 i_0 u_1))/\(not (tree_member  it_0 i_0))/\(u_0 = i_0)/\(not (u_1 = i_0))/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_1 u_1 u_0))/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_2 i_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t49 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(tree_left  it_1 u_0 u_1)/\(not (u_0 = i_0))/\(not (u_1 = i_0))/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_left  it_1 u_1 u_0))/\(tree_member  it_1 u_0)/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (tree_left  it_2 u_0 u_1)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t50 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_1 u_0))/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_1 u_1 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t51 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_1 u_0))/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_2 u_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t52 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_left  it_2 u_1 u_0)/\(not (tree_member  it_1 u_0))/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (u_1 = i_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t53 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((tree_left  it_2 u_1 u_0)/\(not (tree_member  it_1 u_0))/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (tree_member  it_0 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t54 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = i_0))/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_member  it_1 u_0))/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_1 u_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t55 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = i_0))/\(not (tree_member  it_2 u_0))/\(not (tree_left  it_2 u_1 u_0))/\(not (tree_member  it_1 u_0))/\(tree_member  it_1 u_1)/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_member  it_0 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t56 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_1 u_1))/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_2 u_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t57 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_1 u_1))/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (u_1 = i_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t58 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (i_0 = u_0))/\(not (tree_member  it_1 u_1))/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_1 u_0 i_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t59 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (i_0 = u_0))/\(not (tree_member  it_1 u_1))/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_0 u_0 i_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t60 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (i_0 = u_0))/\(not (tree_member  it_1 u_1))/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_1 i_0 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t61 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (i_0 = u_0))/\(tree_left  it_2 i_0 u_0)/\(tree_member  it_2 u_0)/\(not (tree_member  it_1 u_1))/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (tree_member  it_0 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t62 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (i_0 = u_0))/\(not (tree_left  it_2 i_0 u_0))/\(tree_member  it_2 u_0)/\(not (tree_member  it_1 u_1))/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_member  it_0 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t63 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (i_0 = u_0))/\(not (tree_member  it_2 u_0))/\(not (tree_member  it_1 u_1))/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_member  it_0 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t64 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (i_0 = u_0))/\(not (tree_member  it_2 u_0))/\(not (tree_member  it_1 u_1))/\(not (tree_member  it_0 u_1))/\(tree_member  it_2 u_1)) -> (not (tree_left  it_2 i_0 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t65 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_1))) -> (not (tree_member  it_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t66 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_1))) -> (not (tree_left  it_2 u_1 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t67 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_1))) -> (not (tree_member  it_1 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t68 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_1))) -> (not (u_1 = i_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t69 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_1))) -> (not (tree_left  it_0 u_1 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t70 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_1))) -> (not (tree_left  it_1 u_1 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t71 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_1))) -> (not (tree_left  it_0 u_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t72 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_1))) -> (not (tree_left  it_1 u_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t73 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (tree_member  it_2 u_1))) -> (not (tree_left  it_2 u_0 u_1))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t74 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(not (u_0 = i_0))/\(not (tree_member  it_0 u_0))/\(tree_member  it_2 u_0)/\(not (tree_member  it_2 u_1))) -> (tree_member  it_1 u_0)).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t75 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(not (tree_member  it_2 u_0))/\(not (tree_member  it_2 u_1))) -> (not (u_0 = i_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t76 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(not (tree_member  it_2 u_0))/\(not (tree_member  it_2 u_1))) -> (not (tree_member  it_0 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma unbset3consistent_t77 (it_0:tree nat) (i_0:nat) (it_1:tree nat) (it_2:tree nat) (u_0:nat) (u_1:nat) : (t_spec  it_0 i_0 it_1 it_2) -> (((not (u_1 = u_0))/\(not (tree_member  it_2 u_0))/\(not (tree_member  it_2 u_1))) -> (not (tree_member  it_1 u_0))).
Proof. solve_t; try (assert (u_0 = u_1); subst; eauto). Qed.

