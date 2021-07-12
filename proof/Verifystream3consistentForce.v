Require Import ListAux.
Require Import TreeAux.
Require Import Tactics.
Lemma stream3consistent_Force0 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((list_member  il_1 u_1)) -> (list_member  il_0 u_1)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Force1 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_once  il_0 u_1))/\(list_order  il_0 u_1 u_0)/\(list_member  il_1 u_1)) -> (list_order  il_1 u_1 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Force2 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_once  il_0 u_1))/\(not (list_order  il_0 u_0 u_1))/\(list_order  il_0 u_1 u_0)/\(list_member  il_1 u_1)) -> (not (list_order  il_1 u_0 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Force3 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Force4 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_order  il_0 u_0 u_1))/\(list_member  il_0 u_0)/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)) -> (u_1 = u_0)).
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

Lemma stream3consistent_Force5 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_order  il_0 u_0 u_1))/\(list_member  il_0 u_0)/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)) -> (list_once  il_1 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Force6 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_order  il_0 u_0 u_1))/\(list_once  il_0 u_1)/\(not (list_member  il_0 u_0))/\(not (list_order  il_0 u_1 u_0))/\(list_member  il_1 u_1)) -> (list_once  il_1 u_1)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Force7 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_once  il_0 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Force8 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_member  il_0 u_1))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Force9 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (list_member  il_1 u_1))) -> (not (list_order  il_1 u_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Force10 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(list_once  il_0 u_0)/\(not (list_member  il_1 u_1))) -> (list_once  il_1 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Force11 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(not (list_once  il_0 u_0))/\(not (list_member  il_1 u_1))) -> (not (list_once  il_1 u_0))).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma stream3consistent_Force12 (il_0:list nat) (il_1:list nat) (u_0:nat) (u_1:nat) : (id_spec  il_0 il_1) -> (((not (u_1 = u_0))/\(list_member  il_0 u_0)/\(not (list_once  il_0 u_0))/\(not (list_member  il_1 u_1))) -> (list_member  il_1 u_0)).
Proof. solve_id; try (assert (u_0 = u_1); subst; eauto). Qed.

