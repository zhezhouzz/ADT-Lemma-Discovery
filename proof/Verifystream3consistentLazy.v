Require Import ListAux.
Require Import TreeAux.
Require Import Tactics.
Lemma stream3consistent_Lazy0 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_member  il_1 u_1)) -> (list_member  il_0 u_1)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy1 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_order  il_0 u_1 u_0)/\(list_member  il_1 u_1)) -> (list_order  il_1 u_1 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy2 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((u_1 = u_0)/\(list_order  il_0 u_1 u_0)/\(list_member  il_1 u_1)) -> (not (list_once  il_0 u_0))).
Proof. solve_id. apply lord_once_3 in H0. auto. Qed.

Lemma stream3consistent_Lazy3 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_order  il_0 u_0 u_1)/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)) -> (list_member  il_0 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy4 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_member  il_1 u_0)/\(not (list_order  il_0 u_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)) -> (u_1 = u_0)).
Proof.
  intro pushspec;
    inversion pushspec as [a b Hhd Hmem Hord Honce]; subst;
      try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hord; try setoid_rewrite Honce;
        clear Hhd Hmem Hord Honce;
        repeat ((repeat setoid_rewrite rewrite_not_conj);
                (repeat setoid_rewrite rewrite_not_disj);
                (repeat setoid_rewrite rewrite_not_not));
        intros; try (match goal with
                     | _ : _ |- not _ => intro
                     end); destruct_pairs. apply (lord_ord_mem1 il_0); auto. Qed.

Lemma stream3consistent_Lazy5 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_member  il_1 u_0)/\(not (list_order  il_0 u_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)) -> (list_once  il_0 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy6 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_member  il_1 u_0)/\(not (list_order  il_0 u_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)) -> (list_once  il_1 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy7 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_0))/\(not (list_order  il_0 u_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_once  il_0 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy8 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_0))/\(not (list_order  il_0 u_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (u_1 = u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy9 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_once  il_0 u_1)/\(not (list_member  il_1 u_0))/\(not (list_order  il_0 u_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)) -> (list_once  il_1 u_1)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy10 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_once  il_0 u_1))/\(not (list_member  il_1 u_0))/\(not (list_order  il_0 u_0 u_1))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_once  il_1 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy11 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_once  il_0 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy12 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_member  il_0 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy13 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_order  il_0 u_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy14 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_once  il_1 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy15 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_1 u_1))) -> (not (list_order  il_0 u_0 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy16 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(list_member  il_0 u_0)/\(not (list_member  il_1 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy17 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(list_once  il_0 u_0)/\(list_member  il_0 u_0)/\(not (list_member  il_1 u_1))) -> (list_once  il_1 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy18 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_once  il_0 u_0))/\(list_member  il_0 u_0)/\(not (list_member  il_1 u_1))) -> (not (list_once  il_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy19 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_0 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_once  il_0 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy20 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_0 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_once  il_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Lazy21 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_member  il_0 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_member  il_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

