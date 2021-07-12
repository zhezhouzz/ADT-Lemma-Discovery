Require Import ListAux.
Require Import TreeAux.
Require Import Tactics.
Lemma customstk3consistent_top0 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((u_0 = i_0)/\(u_1 = u_0)/\(list_member  il_0 u_1)) -> (list_head  il_0 i_0)).
Proof. solve_top; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_top1 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((not (u_0 = i_0))/\(u_1 = u_0)/\(list_member  il_0 u_1)) -> (not (list_head  il_0 u_0))).
Proof. solve_top; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_top2 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((u_1 = i_0)/\(not (u_1 = u_0))/\(list_member  il_0 u_1)) -> (list_head  il_0 i_0)).
Proof. solve_top; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_top3 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((u_1 = i_0)/\(not (u_1 = u_0))/\(list_member  il_0 u_1)) -> (not (list_head  il_0 u_0))).
Proof. solve_top; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_top4 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((list_member  il_0 u_0)/\(u_1 = i_0)/\(not (u_1 = u_0))/\(list_member  il_0 u_1)) -> (list_order  il_0 i_0 u_0)).
Proof. solve_top; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_top5 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((not (list_member  il_0 u_0))/\(u_1 = i_0)/\(not (u_1 = u_0))/\(list_member  il_0 u_1)) -> (not (list_order  il_0 i_0 u_0))).
Proof.
    intro pushspec;
  inversion pushspec as [a b Hhd]; subst; intros; destruct_pairs;
  try (match goal with
       | x: nat, y: nat, z: nat |- _ => destruct (Hhd x); destruct (Hhd y); destruct (Hhd z)
       | x: nat, y: nat |- _ => destruct (Hhd x); destruct (Hhd y)
       | x: nat |- _ => destruct (Hhd x)
       end). eauto.
Qed.

Lemma customstk3consistent_top6 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((not (list_member  il_0 u_0))/\(u_1 = i_0)/\(not (u_1 = u_0))/\(list_member  il_0 u_1)) -> (not (list_order  il_0 u_0 i_0))).
Proof.
    intro pushspec;
      inversion pushspec as [a b Hhd]; subst; intros; try intr_not; destruct_pairs.
    eauto.
Qed.

Lemma customstk3consistent_top7 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((not (u_1 = i_0))/\(not (u_1 = u_0))/\(list_member  il_0 u_1)) -> (not (list_head  il_0 u_1))).
Proof. solve_top; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_top8 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((list_member  il_0 u_0)/\(u_0 = i_0)/\(not (u_1 = i_0))/\(not (u_1 = u_0))/\(list_member  il_0 u_1)) -> (list_head  il_0 i_0)).
Proof. solve_top; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_top9 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((list_member  il_0 u_0)/\(u_0 = i_0)/\(not (u_1 = i_0))/\(not (u_1 = u_0))/\(list_member  il_0 u_1)) -> (list_order  il_0 i_0 u_1)).
Proof. solve_top; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_top10 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((list_member  il_0 u_0)/\(not (u_0 = i_0))/\(not (u_1 = i_0))/\(not (u_1 = u_0))/\(list_member  il_0 u_1)) -> (not (list_head  il_0 u_0))).
Proof. solve_top; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_top11 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((not (list_member  il_0 u_1))) -> (not (u_1 = i_0))).
Proof. solve_top; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_top12 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((not (list_member  il_0 u_1))) -> (not (list_order  il_0 u_1 u_0))).
Proof. intros. intro.
       eauto. Qed.

Lemma customstk3consistent_top13 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((u_0 = i_0)/\(not (list_member  il_0 u_1))) -> (list_member  il_0 i_0)).
Proof. solve_top; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_top14 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((u_0 = i_0)/\(not (list_member  il_0 u_1))) -> (list_head  il_0 i_0)).
Proof. solve_top; try (assert (u_0 = u_1); subst; eauto). Qed.

Lemma customstk3consistent_top15 (il_0:list nat) (i_0:nat) (u_0:nat) (u_1:nat) : (top_spec  il_0 i_0) -> (((u_0 = i_0)/\(not (list_member  il_0 u_1))) -> (not (list_order  il_0 i_0 u_1))).
Proof. intros. intro. destruct H0. eauto. Qed.

