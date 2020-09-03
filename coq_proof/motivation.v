Require Import List.

Inductive reach: (nat -> nat -> Prop) -> nat -> nat -> Prop :=
| reach1: forall (p:nat -> nat -> Prop) u v, p u v -> reach p u v
| reach2: forall (p:nat -> nat -> Prop) u v w, p u w -> reach p w v -> reach p u v.

Hint Constructors reach.

Inductive reachk: (nat -> nat -> Prop) -> list nat -> nat -> nat -> Prop :=
| reachk1: forall (p:nat -> nat -> Prop) u v, p u v -> reachk p nil u v
| reachk2: forall (p:nat -> nat -> Prop) u v mid w,
      p u w /\ reachk p mid w v -> reachk p (w::mid) u v.

Hint Constructors reachk.

Lemma reachk_to_reach: forall p mid u v,
    reachk p mid u v -> reach p u v.
Proof.
  intro p; intro mid.
  induction mid; intros; inversion H; subst; auto.
  - destruct H5. apply IHmid in H1. eauto. 
Qed.

Lemma reach_to_reachk: forall p u v,
    reach p u v -> exists mid, reachk p mid u v.
Proof.
  intros.
  induction H; subst.
  - exists nil. auto.
  - destruct IHreach. assert (reachk p (w::x) u v).
    auto. eauto.
Qed.

Lemma unique (p: nat -> nat -> Prop):
  (forall x, ~ (reach p x x)) -> (forall x, ~ (p x x)).
Proof.
  intros.
  intro.
  assert (~ reach p x x). apply H. apply H1. apply reach1. auto.
Qed.

Lemma transk (p: nat -> nat -> Prop):
  (forall midxy x y z midyz, (reachk p midxy x y) /\ (reachk p midyz y z) -> exists midxz, (reachk p midxz x z)).
Proof.
  intro midxy.
  induction midxy; intros.
  - exists (cons y midyz). destruct H. inversion H; eauto.
  - destruct H. inversion H; subst.
    destruct H6.
    (assert (exists midxz : list nat, reachk p midxz a z)). eauto.
    destruct H3.
    exists (a :: x0). eauto.
Qed.

Lemma trans (p: nat -> nat -> Prop):
  (forall x y z, (reach p x y) -> (reach p y z) -> (reach p x z)).
Proof.
  intros. apply reach_to_reachk in H. apply reach_to_reachk in H0.
  destruct H.
  destruct H0.
  assert (exists midxz, (reachk p midxz x z)). eapply transk. eauto.
  destruct H1. apply reachk_to_reach in H1. auto.
Qed.

Lemma reach_iff_next (l1_next: nat -> nat -> Prop) (l2_next: nat -> nat -> Prop):
  (forall x y, (reach l1_next x y) <-> (reach l2_next x y)) ->
  (forall x, ~ (reach l1_next x x)) ->
  (forall x y z, (l1_next x y) /\ (l1_next x z) -> y = z) ->
  (forall u v, l1_next u v -> l2_next u v).
Proof.
  intros.
  (assert (reach l2_next u v)). apply H. apply reach1. auto.
  inversion H3; subst.
  - auto.
  - assert (HA := H4).
    rewrite <- H in H5.
    apply reach1 in H4.
    rewrite <- H in H4.
    inversion H4; subst.
    + assert (w = v). eauto. rewrite <- H7. auto.
    + assert (w0 = v). eauto. rewrite H8 in H7.
      assert (HK := trans _ _ _ _ H7 H5). apply H0 in HK. inversion HK.
Qed.

Lemma motivation (l1_next: nat -> nat -> Prop) (l2_next: nat -> nat -> Prop):
  (forall x y, (reach l2_next x y -> reach l1_next x y) /\ (reach l1_next x y /\ ~(reach l1_next y x) -> reach l2_next x y)) ->
  (forall x, ~ (reach l1_next x x)) ->
  (forall x y z, (l1_next x y) /\ (l1_next x z) -> y = z) ->
  (forall u v, l1_next u v -> l2_next u v).
Proof.
  intros.
  assert (forall x y, reach l1_next x y <-> reach l2_next x y).
  - intros. destruct (H x y). split; auto.
    + intros. apply H4. split; auto. intro. apply (H0 x). apply trans with y; auto.
  - apply (reach_iff_next l1_next l2_next); auto.
Qed.
