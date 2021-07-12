Require Import List.
Require Import Tactics.
Require Import Arith.
Import ListNotations.

Require Import Logic.ClassicalFacts.

Axiom excluded_middle: excluded_middle.
Lemma rewrite_not_conj P Q: not (P /\ Q) <-> (not P) \/ (not Q).
Proof.
  split; intros; auto.
  - destruct (excluded_middle P).
    + right. intro. auto.
    + left. auto.
  - intro. destruct H0. destruct H; auto.
Qed.
Lemma rewrite_not_not P: not (not P) <-> P.
Proof.
  split; intros; auto.
  - destruct (excluded_middle P); auto.
    exfalso. auto.
Qed.

Inductive list_head : list nat -> nat -> Prop :=
| lhd1: forall u u', u = u' -> list_head [u] u'
| lhd2: forall l u u', u = u' ->  list_head (u :: l) u'.

Inductive list_member: list nat -> nat -> Prop :=
| lmem1: forall l u u', u = u' -> list_member (u :: l) u'
| lmem2: forall l u v, list_member l u -> list_member (v :: l) u.

Inductive list_order: list nat -> nat -> nat -> Prop :=
| lord1: forall l u u' v, u = u' -> list_member l v -> list_order (u :: l) u' v
| lord2: forall l u v w, list_order l u v -> list_order (w :: l) u v.

Inductive list_once: list nat -> nat -> Prop :=
| lonce1: forall l u u', u = u' -> not (list_member l u) -> list_once (u :: l) u'
| lonce2: forall l u u', u <> u' -> list_once l u' -> list_once (u :: l) u'.

Hint Constructors list_head: core.
Hint Constructors list_member: core.
Hint Constructors list_order: core.
Hint Constructors list_once: core.

Ltac invsub H := inversion H; subst.

Lemma lord_one_elem: forall (u: nat) (v: nat) (w: nat), not (list_order [w] u v).
Proof.
  unfold not. intros. invsub H.
  - inversion H5.
  - inversion H4.
Qed.

Hint Resolve lord_one_elem: core.

Lemma lmem_one_elem: forall (u: nat) (v: nat) , list_member [u] v -> u = v.
Proof.
  intros. invsub H; auto. inversion H3.
Qed.

Hint Resolve lord_one_elem: core.

Lemma lhd_lmem1: forall (l: list nat) (u: nat), list_head l u -> list_member l u.
Proof.
  intros.
  destruct H; auto with core.
Qed.

Hint Resolve lhd_lmem1: core.

Lemma lhd: forall (l: list nat) (u: nat) (v: nat), list_head l u -> list_head l v -> u = v.
Proof.
  intros. destruct l.
  - inversion H.
  - inversion H; inversion H0; subst; auto.
Qed.

Hint Resolve lhd: core.

Lemma lord_lmem1: forall (l: list nat) (u: nat) (v: nat), list_order l u v -> list_member l u.
Proof.
  intros. induction H; subst; auto.
Qed.

Lemma lord_lmem2: forall (l: list nat) (u: nat) (v: nat), list_order l u v -> list_member l v.
Proof.
intros.
  induction H; subst; auto.
Qed.

Hint Resolve lord_lmem1: core.
Hint Resolve lord_lmem2: core.

Lemma lord_lhd3: forall (l: list nat) (u: nat) (v: nat), list_head l u -> not (list_order l u v) -> not (u = v) -> not (list_member l v).
Proof.
  intros. destruct H.
  - intro. apply lmem_one_elem in H2. subst. auto.
  - intro. invsub H2.
    + auto.
    + auto.
Qed.

Lemma lord_lhd4: forall (l: list nat) (u: nat) (v: nat), list_member l u -> list_member l v -> not (u = v) -> not (list_order l u v) -> list_order l v u.
Proof.
  intros. induction l.
  - inversion H.
  - destruct (Nat.eqb_spec a v); subst.
    + invsub H. exfalso; auto. auto.
    + apply lord2. invsub H0. exfalso; auto.
      destruct (Nat.eqb_spec a u); subst.
      exfalso. auto.
      invsub H. exfalso; auto.
      auto.
Qed.

Lemma lord_lhd5: forall (l: list nat) (u: nat) (v: nat), list_member l u -> list_member l v -> not (u = v) -> not (list_order l v u) -> list_order l u v.
Proof.
  intros. apply lord_lhd4; auto.
Qed.

Lemma lord_lhd6: forall (l: list nat) (u: nat) (v: nat), list_member l u -> list_member l v -> not (list_order l v u) -> not (list_order l u v) -> (u = v).
Proof.
  intros.
  destruct (Nat.eqb_spec u v); subst; auto.
  exfalso. apply H2. apply (lord_lhd4 l); auto.
Qed.

Hint Resolve lord_lhd3: core.
Hint Resolve lord_lhd4: core.
Hint Resolve lord_lhd5: core.
Hint Resolve lord_lhd6: core.

Lemma lonce_mem1: forall (l: list nat) (u: nat), list_once l u -> list_member l u.
Proof.
  intros.
  induction H; subst; auto.
Qed.

Hint Resolve lonce_mem1: core.

(* Lemma lord_ord_1: forall (l: list nat) (u: nat) (v: nat), list_order l u v -> not (list_order l v u) -> (u = v). *)
(* Proof. *)
(* Admitted. *)

(* Hint Resolve lord_ord_1: core. *)

Lemma lord_once_1: forall (l: list nat) (u: nat) (v: nat), u = v -> list_order l u v -> not (list_once l u).
Proof.
  intros.
  intro. subst. induction H1; subst.
  - induction l.
    + eapply lord_one_elem. apply H0.
    + destruct (Nat.eqb_spec a u'). subst. auto.
      apply IHl.
      inversion H0; subst. invsub H6; auto. invsub H5; auto. intro. apply H1; auto.
  - invsub H0; auto.
Qed.

Lemma lord_once_2: forall (l: list nat) (u: nat) (v: nat), u = v -> list_order l u v -> not (list_once l v).
Proof.
  intros.
  intro. subst. induction H1.
  - subst. apply H1. invsub H0; eauto.
  - apply IHlist_once. invsub H0; auto.
Qed.

Lemma lord_once_3: forall (l: list nat) (u: nat), list_once l u -> not (list_order l u u).
Proof.
  intros.
  induction H; auto.
  intro. invsub H1; auto. apply H0; eauto.
  intro. invsub H1; auto.
Qed.

Hint Resolve lord_once_1: core.
Hint Resolve lord_once_2: core.
Hint Resolve lord_once_3: core.

Lemma lmem_ord_once_1: forall (l: list nat) (u: nat) (v: nat),
    list_member l u -> list_member l v ->
    not (list_order l u v) -> not (list_order l v u) ->
    list_once l u.
Proof.
  intros. assert (u = v). apply (lord_lhd6 l); auto. subst.
  induction l.
  - inversion H.
  - destruct (Nat.eqb_spec a v); subst; auto.
    apply lonce2; auto. apply IHl; auto.
    + invsub H; auto. exfalso. auto.
    + invsub H; auto. exfalso. auto.
Qed.

Lemma lmem_ord_once_2: forall (l: list nat) (u: nat) (v: nat),
    list_member l u -> list_member l v ->
    not (list_order l u v) -> not (list_order l v u) ->
    list_once l v.
Proof.
  intros.
  eapply lmem_ord_once_1; auto. apply H. auto. auto.
Qed.

Hint Resolve lmem_ord_once_1: core.
Hint Resolve lmem_ord_once_2: core.

Lemma lhd_mem_ord_1: forall (l: list nat) (u: nat) (v: nat),
    list_head l u -> not (u = v) -> list_member l v -> list_order l u v.
Proof.
  intros.
  destruct H.
  - invsub H1; auto.
  - invsub H1; auto.
Qed.

Lemma lhd_mem_ord_2: forall (l: list nat) (u: nat) (v: nat),
    list_head l u /\ not (list_order l u v) /\ (list_member l v) -> u = v.
Proof.
  intros. destruct (Nat.eqb_spec u v); subst; auto.
  exfalso. destruct_pairs. apply H0; auto. apply lhd_mem_ord_1; auto.
Qed.

Hint Resolve lhd_mem_ord_1: core.
Hint Resolve lhd_mem_ord_2: core.

Lemma lord_ord_mem1: forall (l: list nat) (u: nat) (v: nat),
    not (list_order l u v) -> not (list_order l v u) -> list_member l u -> list_member l v -> u = v.
Proof.
  intros. apply (lord_lhd6 l); auto.
Qed.

Lemma lord_ord_mem2: forall (l: list nat) (u: nat) (v: nat),
   list_member l u -> list_member l v -> not (u = v) -> not (list_order l u v) -> list_order l v u.
Proof.
  intros. apply (lord_lhd5 l); auto.
Qed.

Lemma lord_ord_mem3: forall (l: list nat) (u: nat) (v: nat),
   list_member l u -> list_member l v -> not (u = v) -> not (list_order l v u) -> list_order l u v.
Proof.
  intros. apply (lord_lhd5 l); auto.
Qed.

Hint Resolve lord_ord_mem1: core.
Hint Resolve lord_ord_mem2: core.
Hint Resolve lord_ord_mem3: core.


Hint Unfold not: core.

Lemma rewrite_not_disj P Q: not (P \/ Q) <-> (not P) /\ (not Q).
Proof. split; auto. intros. intro. destruct H. destruct H0; contradiction. Qed.

Inductive push_spec: nat -> list nat -> list nat -> Prop :=
| canonical_push_spec: forall x l l',
    (forall u, list_head l' u <-> u = x) ->
    (forall u, list_member l' u <-> ((u = x) \/ (list_member l u))) ->
    (forall u v, list_order l' u v <->
            ((list_order l u v) \/ ((u = x) /\ (list_member l v)))) ->
    (forall u, list_once l' u <->
             (((u <> x) /\ (list_once l u)) \/ ((u = x) /\ not (list_member l u)))) ->
    push_spec x l l'.

Definition push (x: nat) (l: list nat): list nat := x :: l.

Lemma push_push_spec: forall x l l', (push x l = l') -> (push_spec x l l').
Proof.
  unfold push. intros. subst.
  apply canonical_push_spec; intro.
  - split; auto. intro. invsub H; auto.
  - split; intros; auto; invsub H; auto.
  - split; intros; auto; invsub H; auto. destruct_pairs. subst.
    destruct H; auto.
  - split; intros; auto; invsub H; auto; destruct_pairs; subst; auto.
Qed.

Inductive nil_spec: list nat -> Prop :=
| canonical_nil_spec: forall l',
    (forall u, not (list_head l' u)) ->
    (forall u, not (list_member l' u)) ->
    (forall u v, not (list_order l' u v)) ->
    (forall u, not (list_once l' u)) ->
    nil_spec l'.

Definition nil: list nat := [].

Lemma nil_nil_spec: (nil_spec nil).
Proof.
  unfold nil. intros. subst.
  apply canonical_nil_spec; intro;
    try (split; intros; auto; invsub H; auto; destruct_pairs; subst; auto);
    try (intros; intro; inversion H).
Qed.

Inductive id_spec: list nat -> list nat -> Prop :=
| canonical_id_spec: forall l l',
    (forall u, list_head l' u <-> list_head l u) ->
    (forall u, list_member l' u <-> list_member l u) ->
    (forall u v, list_order l' u v <-> list_order l u v) ->
    (forall u, list_once l' u <-> list_once l u) ->
    id_spec l l'.

Definition id (l: list nat): list nat := l.

Lemma id_id_spec: forall l l', (id l = l') -> (id_spec l l').
Proof.
  unfold id. intros. subst.
  apply canonical_id_spec; intro;
     try (split; intros; auto; invsub H; auto; destruct_pairs; subst; auto);
    try (intros; intro; inversion H).
Qed.


Inductive is_empty_spec: list nat -> bool ->  Prop :=
| canonical_is_empty_spec: forall l' b,
    (forall u, Bool.Is_true b -> not (list_head l' u)) ->
    (forall u, Bool.Is_true b -> not (list_member l' u)) ->
    (forall u v, Bool.Is_true b -> not (list_order l' u v)) ->
    (forall u, Bool.Is_true b ->  not (list_once l' u)) ->
    is_empty_spec l' b.

Definition is_empty (l: list nat): bool :=
  match l with
  | [] => true
  | _ => false
  end.

Lemma is_empty_is_empty_spec: forall l l', (is_empty l = l') -> (is_empty_spec l l').
Proof.
  unfold is_empty. intros. subst.
  apply canonical_is_empty_spec; intro.
  induction l; intros.
  - intro. inversion H0.
  - inversion H.
  - destruct l; intros.
    + intro. inversion H0.
    + inversion H.
  - intros. intro. destruct l; intros. inversion H0. inversion H.
  - intros. intro. destruct l; intros. inversion H0. inversion H.
Qed.

Inductive top_spec: list nat -> nat -> Prop :=
| canonical_top_spec: forall l x,
    (forall u, u = x <-> list_head l u ) ->
    top_spec l x.

Definition top (l: list nat): option nat :=
  match l with
  | [] => None
  | h :: _ => Some h
  end.

Lemma top_top_spec: forall x l, ((top l) = Some x) -> (top_spec l x).
Proof.
  unfold top. intros. subst.
  apply canonical_top_spec; intro.
  destruct l.
  - inversion H.
  - split; auto; intros; invsub H; auto. invsub H0; auto.
Qed.

Inductive tail_spec: list nat -> list nat -> Prop :=
| canonical_tail_spec: forall l l',
    (forall u , list_head l' u -> (list_member l u)) ->
    (forall u , list_member l' u -> (list_member l u)) ->
    (forall u v, list_order l' u v -> list_order l u v) ->
    (forall u, list_once l' u ->
          ((not (list_head l u) /\ (list_once l u)) \/ ((list_head l u) /\ not (list_once l u) /\ (list_member l u)))) ->
    (forall u, ((list_member l u) /\ not (list_member l' u)) -> list_head l u) ->
    (forall u v, (list_order l u v /\ not (list_head l u)) -> list_order l' u v) ->
    (forall u, (list_head l u /\ not (list_member l' u)) -> not (list_order l u u)) ->
    tail_spec l l'.

Definition tail (l: list nat): option (list nat) :=
  match l with
  | [] => None
  | h :: t => Some t
  end.

Lemma tail_tail_spec: forall l l', ((tail l) = Some l') -> (tail_spec l l').
Proof.
  unfold tail. intros. subst.
  apply canonical_tail_spec.
  - induction l; invsub H; intros; auto.
  - induction l; invsub H; intros; auto.
  - induction l; invsub H; intros; auto.
  - induction l; invsub H; intros; auto.
    destruct (Nat.eqb_spec a u).
    + subst. right. split; auto. split; auto. intro. invsub H1; auto.
    + left. split; auto. intro. invsub H1; auto.
  - induction l; invsub H; intros; auto.
    destruct_pairs. invsub H0; auto. exfalso; auto.
  - destruct l; invsub H; intros; auto.
    destruct_pairs. inversion H0; subst; auto.
    exfalso; auto.
  - destruct l; invsub H; intros; auto.
    destruct_pairs. invsub H0; auto.
Qed.

Inductive concat_spec: list nat -> list nat -> list nat ->  Prop :=
| canonical_concat_spec: forall l1 l2 l',
    (forall u, list_head l' u -> (list_head l1 u \/ list_head l2 u)) ->
    (forall u, list_member l' u <-> (list_member l1 u \/ list_member l2 u)) ->
    (forall u v, list_order l' u v <-> (list_order l1 u v \/ list_order l2 u v \/ (list_member l1 u /\ list_member l2 v))) ->
    (forall u, list_once l' u <-> ((list_once l1 u /\ not (list_member l2 u)) \/
                              (list_once l2 u /\ not (list_member l1 u)))) ->
    concat_spec l1 l2 l'.

Definition concat (l1: list nat) (l2: list nat): list nat := l1 ++ l2.

Lemma concat_concat_spec2: forall l1 l2,
    (forall u, list_member (l1 ++ l2) u <-> (list_member l1 u \/ list_member l2 u)).
Proof.
  unfold concat. intros. subst.
  split; intros; auto.
  + induction l1; auto.
    destruct (Nat.eqb_spec a u); auto.
    invsub H. exfalso; auto.
    apply IHl1 in H3. destruct H3.
    left; auto. right; auto.
  + induction l1; auto.
    destruct H. inversion H. auto.
    destruct (Nat.eqb_spec a u); subst; simpl; auto.
    simpl. apply lmem2. apply IHl1.
    destruct H. left; auto. invsub H; auto. exfalso; auto. right; auto.
Qed.

Lemma concat_concat_spec1: forall l1 l2,
    (forall u, list_head (l1 ++ l2) u -> (list_head l1 u \/ list_head l2 u)).
Proof.
  unfold concat. intros.
  intros; destruct l1; auto. left. simpl in H. inversion H; subst; auto.
Qed.

Lemma concat_concat_spec1': forall l1 l2,
    (forall u, list_head (l1 ++ l2) u -> (list_head l1 u \/ (list_head l2 u /\ l1 = []) )).
Proof.
  unfold concat. intros.
  intros; destruct l1; auto. invsub H.
  - destruct l1; auto.
  - simpl in H. invsub H; auto.
Qed.

Lemma concat_concat_spec3: forall l1 l2,
    (forall u v, list_order (l1 ++ l2) u v <-> (list_order l1 u v \/ list_order l2 u v \/ (list_member l1 u /\ list_member l2 v))).
Proof.
  unfold concat. intros. subst.
  split; intros; auto.
  + induction l1; invsub H; auto.
    rewrite concat_concat_spec2 in H5.
    destruct H5. left. auto. right. right. auto.
    apply IHl1 in H4.
    destruct H4. left; auto. destruct H0. right. left. auto.
    destruct H0. right. right. auto.
  + destruct H.
    induction H; subst; auto. simpl; auto. apply lord1; auto. rewrite concat_concat_spec2.
    left. auto.
    simpl. auto.
    induction l1. simpl. destruct H; auto. destruct H. inversion H.
    destruct (Nat.eqb_spec a u). subst. simpl; auto.
    destruct H. apply lord2. apply IHl1. left; auto. apply lord1; auto. rewrite concat_concat_spec2. right. destruct H. auto.
    apply lord2. apply IHl1. destruct H. left; auto. destruct H. invsub H; auto. exfalso; auto.
Qed.

Lemma concat_concat_spec4: forall l1 l2,
    (forall u, list_once (l1 ++ l2) u <-> ((list_once l1 u /\ not (list_member l2 u)) \/
                              (list_once l2 u /\ not (list_member l1 u)))).
Proof.
  unfold concat. intros. subst.
   split; intros; auto.
    + induction l1; subst; auto. simpl in H. right. split; auto. intro. inversion H0.
      destruct (Nat.eqb_spec a u); subst. invsub H; subst. left. split; auto. apply lonce1; auto. intro. apply H4. rewrite concat_concat_spec2. auto. intro. apply H4. rewrite concat_concat_spec2. auto. exfalso. auto. invsub H. exfalso. auto.
      apply IHl1 in H4. destruct H4. left. destruct H0. split; auto.
      destruct H0. right. split; auto. intro. invsub H3. exfalso; auto. auto.
    + destruct H. destruct H. induction H; subst. simpl. apply lonce1; auto. intro. rewrite concat_concat_spec2 in H. tauto. simpl. apply lonce2; auto. destruct H. induction l1; auto. simpl. apply lonce2. intro. subst. apply H0; auto. apply IHl1. intro. auto.
Qed.

Lemma concat_concat_spec: forall l1 l2 l', (concat l1 l2 = l') -> (concat_spec l1 l2 l').
Proof.
  unfold concat. intros. subst.
  apply canonical_concat_spec; intro.
  - intros; destruct l1; auto. left. simpl in H. inversion H; subst; auto.
  - rewrite concat_concat_spec2. reflexivity.
  - intros. rewrite -> concat_concat_spec3. reflexivity.
  - intros. rewrite -> concat_concat_spec4. reflexivity.
Qed.

Inductive reverse_spec: list nat -> list nat -> Prop :=
| canonical_reverse_spec: forall l l',
    (forall u, list_head l' u -> list_member l u) ->
    (forall u, list_member l' u <-> list_member l u) ->
    (forall u v, list_order l' u v <-> list_order l v u) ->
    (forall u, list_once l' u <-> list_once l u) ->
    (* (forall u v, list_order l u v /\ not (u = v) -> not (list_head l' u)) -> *)
    (forall u v, list_head l' u -> list_member l v -> not (u = v) -> list_order l v u) ->
    reverse_spec l l'.

Lemma reverse_reverse_spec_mem: forall l, (forall u, list_member (rev l) u <-> list_member l u).
Proof.
  intros. split; subst; intros; auto.
  + induction l; intros; auto. simpl in H. rewrite concat_concat_spec2 in H.
    destruct H; auto. invsub H; auto. inversion H3.
  + induction l; intros; auto. simpl. rewrite concat_concat_spec2.
    invsub H; subst; auto.
Qed.

Lemma reverse_reverse_spec: forall l l', (rev l = l') -> (reverse_spec l l').
Proof.
  intros. subst.
  apply canonical_reverse_spec; intro.
  - induction l; intros; auto. simpl in H. apply concat_concat_spec1 in H.
    destruct H; auto. invsub H; auto.
  - rewrite reverse_reverse_spec_mem. reflexivity.
  - split; subst; intros; auto.
    + induction l; intros; auto. simpl in H. inversion H. simpl in H.
      rewrite concat_concat_spec3 in H.
      destruct H; auto. destruct H. apply lord_one_elem in H. inversion H. destruct H. invsub H0. rewrite reverse_reverse_spec_mem in H. auto. inversion H4.
    + induction l; intros; auto. simpl in H. inversion H. simpl.
      rewrite concat_concat_spec3.
      invsub H; subst. right. right. split; auto. rewrite reverse_reverse_spec_mem; auto. left. auto.
  - split; subst; intros; auto.
    + induction l; intros; auto. simpl in H. rewrite concat_concat_spec4 in H.
      destruct H. destruct H. apply lonce2; auto. destruct H. invsub H; auto. apply lonce1; auto. intro. rewrite <- reverse_reverse_spec_mem in H1. auto. inversion H5.
    + induction l; intros; auto. simpl. rewrite concat_concat_spec4.
      invsub H. right; split; auto. apply lonce1; auto. intro. inversion H0. intro. rewrite reverse_reverse_spec_mem in H0; auto. left. split; auto. intro. invsub H0. invsub H0; auto. inversion H6.
  - intros.
    remember (rev l) as l'. assert (l = rev l').
    rewrite Heql'. rewrite rev_involutive. auto. rewrite H2 in H0. rewrite H2. clear Heql'. clear H2. clear l.
    induction l'. inversion H. invsub H. simpl in H0. invsub H0; auto. inversion H5. clear H. simpl in H0. rewrite concat_concat_spec2 in H0. destruct H0.
    simpl. rewrite concat_concat_spec3. right. right. split; auto.
    invsub H; auto. exfalso; auto. inversion H4.
Qed.


Ltac destruct_disj :=
 match goal with
 | [H : (_ \/ _) |- _] => destruct H
 | [H : _ |- (_ /\ _)] => split
 end.

Ltac solve_eq :=
  match goal with
  | [H : _ |- (_ = _) ] => (try symmetry; auto with core); auto with core
  end.

Ltac solve_not :=
  match goal with
  | [H : _ |- (not _) ] => intro Z
  end; subst; auto with core.

Ltac intr_not :=
  match goal with
  | [_ : _ |- (not _) ] => intro Z
  end.

Ltac solve_disjs := repeat (destruct_disj);
                    destruct_pairs; subst;
                    try contradiction; try solve_eq; try solve_not; auto with core; eauto;
                    try (exfalso; auto with core; eauto).
Ltac solve_push :=
  intro pushspec;
  inversion pushspec as [a b c Hhd Hmem Hord Honce]; subst;
  try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hord; try setoid_rewrite Honce;
  clear Hhd Hmem Hord Honce;
  repeat ((repeat setoid_rewrite rewrite_not_conj);
          (repeat setoid_rewrite rewrite_not_disj);
          (repeat setoid_rewrite rewrite_not_not));
  intros;
  try (match goal with
  | _ : _ |- not _ => intro
  end); destruct_pairs; auto with core; try solve_disjs.

Ltac solve_nil :=
  intro nilspec;
  inversion nilspec as [a Hhd Hmem Hord Honce]; subst; intros;
  try apply Hhd;
  try apply Hmem;
  try apply Hord;
  try apply Honce;
  auto with core.

Ltac solve_id :=
  intro pushspec;
  inversion pushspec as [a b Hhd Hmem Hord Honce]; subst;
  try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hord; try setoid_rewrite Honce;
  clear Hhd Hmem Hord Honce;
  repeat ((repeat setoid_rewrite rewrite_not_conj);
          (repeat setoid_rewrite rewrite_not_disj);
          (repeat setoid_rewrite rewrite_not_not));
  intros; try (match goal with
  | _ : _ |- not _ => intro
  end); destruct_pairs; auto with core; try solve_disjs.

Ltac solve_is_empty :=
  intro nilspec;
  inversion nilspec as [a b Hhd Hmem Hord Honce]; subst; intros;
  try destruct_pairs; auto with core; try solve_disjs;
  try apply Hhd;
  try apply Hmem;
  try apply Hord;
  try apply Honce;
  auto with core; destruct_pairs; auto with core;
  try (match goal with
  | H: (Bool.Is_true _), H' : (list_member _ _) |- _ =>  try (eapply Hmem in H; auto with core)
  | H: (Bool.Is_true _), H' : (list_head _ _) |- _ =>  try (eapply Hhd in H; auto with core)
  | H: (Bool.Is_true _), H' : (list_order _ _) |- _ =>  try (eapply Hord in H; auto with core)
  | H: (Bool.Is_true _), H' : (list_once _ _) |- _ =>  try (eapply Honce in H; auto with core)
  end); try solve_disjs.

Ltac solve_top :=
  intro pushspec;
  inversion pushspec as [a b Hhd]; subst; intros; try intr_not; destruct_pairs;
  try (match goal with
       | x: nat, y: nat, z: nat |- _ => destruct (Hhd x); destruct (Hhd y); destruct (Hhd z)
       | x: nat, y: nat |- _ => destruct (Hhd x); destruct (Hhd y)
       | x: nat |- _ => destruct (Hhd x)
       end); auto with core; eauto; try solve_disjs.

Ltac solve_tail :=
  intro pushspec;
  inversion pushspec as [a b Hhd Hmem Hord Honce Hhd' Hord' Hord'']; subst;
  try apply Hhd';
  intros; destruct_pairs; auto with core; try solve_disjs.

Ltac solve_reverse :=
  intro pushspec;
  inversion pushspec as [a b Hhd Hmem Hord Honce Hhd'']; subst;
  try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hord; try setoid_rewrite Honce;
  clear Hhd Hmem Hord Honce;
  repeat ((repeat setoid_rewrite rewrite_not_conj);
          (repeat setoid_rewrite rewrite_not_disj);
          (repeat setoid_rewrite rewrite_not_not));
  intros; destruct_pairs; auto with core;
  try (match goal with
       | u_0: nat, u_1: nat |- _ =>
         destruct (Nat.eqb_spec u_0 u_1); subst; auto with core; try (eapply Hhd''; auto with core)
       end);
  try solve_disjs.

Ltac solve_concat :=
  intro pushspec;
  inversion pushspec as [a b c Hhd Hmem Hord Honce]; subst;
  try setoid_rewrite Hhd; try setoid_rewrite Hmem; try setoid_rewrite Hord; try setoid_rewrite Honce;
  clear Hhd Hmem Hord Honce;
  repeat ((repeat setoid_rewrite rewrite_not_conj);
          (repeat setoid_rewrite rewrite_not_disj);
          (repeat setoid_rewrite rewrite_not_not));
  intros; destruct_pairs; auto with core;
  try (match goal with
       | u: nat, v: nat |- _ => destruct (Nat.eqb_spec u v); subst; auto with core
       end);
  try solve_disjs.

